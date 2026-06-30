import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

open Simplicial
open CategoryTheory
open SSet

/-!
================================================================================
FILE 1 of 3 — HomotopyRelation.lean
================================================================================

Mathematical goal.  For a quasi-category `X` and vertices `x y`, the parallel
edges `x → y` carry a homotopy relation `f ∼ g`, and this relation is an
equivalence relation (reflexive, symmetric, transitive).  This is Theorem 7.5 of
`source_target_shape_calculus.md`.  The payoff is a `Setoid` on edges, which is
exactly the datum needed to form the quotient hom-sets of the homotopy category
in File 2.

The "element vs. map" dichotomy (read this once; it governs every proof below).
A simplicial set `X` is a functor `Δᵒᵖ → Type`, so an n-simplex has two faces:
  • ELEMENT picture: a point of `X _⦋n⦌`; faces are `SimplicialObject.δ X i`,
    degeneracies are `SimplicialObject.σ X i`.  Our edges and homotopies are
    *defined* here.
  • MAP picture: a morphism `Δ[n] ⟶ X`; "i-th face" means precomposition with
    the coface inclusion `stdSimplex.δ i`.  Mathlib's horn-filling API lives here.
The Yoneda equivalence `yonedaEquiv : (Δ[n] ⟶ X) ≃ X _⦋n⦌` is the dictionary
between the two.  Every horn argument is therefore a SANDWICH: translate the
prescribed faces to maps (`yonedaEquiv.symm`), fill the horn, then translate the
filler back to an element (`yonedaEquiv`) and read off its faces.

Convention (fixed throughout, matching the drafts): for an edge `f`,
  d₁ f = source,   d₀ f = target.
================================================================================
-/

/-- An `Edge X x y` is a 1-simplex together with the proofs that its endpoints
are `x` and `y`.  Bundling the boundary conditions *inside* the object means that
whenever we hold an edge we also hold the evidence about its source and target —
the formal analogue of `Edgeₓ(x,y) = { f ∈ X₁ : d₁f = x, d₀f = y }` (Def. 6.1). -/
structure Edge (X : SSet) (x y : X _⦋0⦌) where
  val  : X _⦋1⦌                              -- the underlying 1-simplex f ∈ X₁
  src  : SimplicialObject.δ X 1 val = x       -- d₁ f = x   (source)
  tgt  : SimplicialObject.δ X 0 val = y       -- d₀ f = y   (target)

/-- The identity edge `1ₓ := s₀ x` (the degenerate 1-simplex on `x`).  Its two
boundary fields are the simplicial identities `d₁ s₀ = id` and `d₀ s₀ = id`.

A recurring "bureaucratic" point: Mathlib states simplicial identities such as
`δ_comp_σ_succ`/`δ_comp_σ_self` as equalities of *maps* in the simplex category.
We need equalities of *elements* (`d₁ s₀ x = x`).  `types_congr_hom h x`
evaluates the map-equality `h` at the point `x`, turning the abstract identity
into the element-level fact we want.  This map→element move appears everywhere. -/
def idEdge (X : SSet) (x : X _⦋0⦌) : Edge X x x where
  val  := SimplicialObject.σ X 0 x
  src  := by                                        -- d₁ (s₀ x) = x   via  d₁ s₀ = id
    have h := SimplicialObject.δ_comp_σ_succ X (i := (0 : Fin 1))
    have h' := types_congr_hom h x
    simpa using h'
  tgt  := by                                        -- d₀ (s₀ x) = x   via  d₀ s₀ = id
    have h := SimplicialObject.δ_comp_σ_self X (i := (0 : Fin 1))
    have h' := types_congr_hom h x
    simpa using h'

/-- The underlying 1-simplex of the identity edge is the degeneracy `s₀ x`.  A
definitional unfolding offered as a citable lemma.  (Deliberately NOT `@[simp]`:
unfolding `(idEdge X x).val` globally rewrites the goals of the symmetry and
transitivity proofs and breaks their downstream `rw`s.) -/
lemma idEdge_val (X : SSet) (x : X _⦋0⦌) :
    (idEdge X x).val = SimplicialObject.σ X 0 x := rfl

/-- Homotopy of parallel edges (Def. 6.2): `f ∼ g` iff there is a 2-simplex `σ`
("homotopy witness") whose three faces are `d₀σ = g`, `d₁σ = f`, `d₂σ = 1ₓ`.
Picture the triangle on vertices `(x, x, y)`: edge `(0,1)` is the identity, edge
`(0,2)` is `f`, edge `(1,2)` is `g`.  We must write `(idEdge X x).val` (the
projection to the underlying 1-simplex) since `δ` returns a raw simplex, not a
bundled `Edge`.  The `[X.Quasicategory]` instance is carried so the relation is
only ever manipulated where symmetry/transitivity are actually available. -/
def Homotopic {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌}
    (f g : Edge X x y) : Prop :=
  ∃ σ : X _⦋2⦌,
    SimplicialObject.δ X 0 σ = g.val ∧
    SimplicialObject.δ X 1 σ = f.val ∧
    SimplicialObject.δ X 2 σ = (idEdge X x).val

/-- Reflexivity (Lemma 7.2), proved with NO horn filling: the witness is the
degenerate 2-simplex `s₀(f)`.  This is the "canary" proof — if the index
conventions (d₁ = source, d₀ = target, and the degeneracy indices) were even
slightly off, this would be the first thing to fail.  The three bullets verify
`d₀ s₀ f = f`, `d₁ s₀ f = f`, and `d₂ s₀ f = s₀(d₁ f) = s₀ x = 1ₓ`; the last one
tests the identity `dᵢ sⱼ = sⱼ dᵢ₋₁` in the case `i > j+1` (here 2 > 0+1). -/
lemma Homotopic.refl {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌}
    (f : Edge X x y) : Homotopic f f := by
  refine ⟨SimplicialObject.σ X 0 f.val, ?_, ?_, ?_⟩
  · have h := SimplicialObject.δ_comp_σ_self X (i := (0 : Fin 2))
    have h' := types_congr_hom h f.val
    simpa using h'
  · have h := SimplicialObject.δ_comp_σ_succ X (i := (0 : Fin 2))
    have h' := types_congr_hom h f.val
    simpa using h'
  · have h := SimplicialObject.δ_comp_σ_of_gt X (j := (0 : Fin 1)) (i := (1 : Fin 2)) (by decide)
    have h' := types_congr_hom h f.val
    simp only [types_comp_apply] at h'
    rw [f.src] at h'
    exact h'

/- ----------------------------------------------------------------------------
The Yoneda bridge.  The next two lemmas are the technical linchpin of the whole
file: they say the element↔map dictionary COMMUTES WITH TAKING FACES.

  • `yonedaEquiv_δ_comp`:  translate-then-apply-δ  =  precompose-coface-then-translate.
  • `δ_comp_yonedaEquiv_symm`:  the same statement for the inverse dictionary
    (the one used to *build* horns from element data).

Concretely, `stdSimplex.δ i ≫ (-)` is "take the i-th face in the map picture"
and `SimplicialObject.δ X i` is "take the i-th face in the element picture".
Without these, one could not legitimately move prescribed faces into the horn
API and read the filler's faces back out.
---------------------------------------------------------------------------- -/
lemma yonedaEquiv_δ_comp {X : SSet} {n : ℕ} (i : Fin (n + 2)) (g : Δ[n + 1] ⟶ X) :
    SSet.yonedaEquiv (stdSimplex.δ i ≫ g) = SimplicialObject.δ X i (SSet.yonedaEquiv g) := by
  rw [SSet.yonedaEquiv_comp]
  have hg : g = SSet.yonedaEquiv.symm (SSet.yonedaEquiv g) := by simp
  nth_rw 1 [hg]
  change (SSet.yonedaEquiv.symm (SSet.yonedaEquiv g)).app _ (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) = _
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  rfl

/-- The inverse-dictionary half of the Yoneda bridge (see the block comment above):
precomposing the map `yonedaEquiv.symm x` with the coface `stdSimplex.δ i` is the
map of the element's `i`-th face.  This is the form used to *build* horns out of
element-level face data. -/
lemma δ_comp_yonedaEquiv_symm {X : SSet} {n : ℕ} (i : Fin (n + 2)) (x : X _⦋n + 1⦌) :
    stdSimplex.δ i ≫ SSet.yonedaEquiv.symm x = SSet.yonedaEquiv.symm (SimplicialObject.δ X i x) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  change (SSet.yonedaEquiv.symm x).app _ (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) = SSet.yonedaEquiv (SSet.yonedaEquiv.symm (SimplicialObject.δ X i x))
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm, Equiv.apply_symm_apply]
  rfl

/-- Symmetry (Lemma 7.3) — the first genuine horn argument, and the template for
all the others.  Given a homotopy `α : f ∼ g`, fill the inner horn `Λ[3,2]` whose
three prescribed faces are
      d₀ = α,      d₁ = s₀(g),      d₃ = s₀(s₀ x),
and read the *missing* face `τ = d₂Ω` of the filler as a homotopy `g ∼ f`.

The proof is the SANDWICH described in the file header:
  1. `yonedaEquiv.symm` moves the three faces `α, s₀ g, s₀(s₀ x)` to the map
     picture (`f₀, f₁, f₃`);
  2. `horn₃₂.desc … h₀₂ h₁₂ h₂₃` assembles them into a map `Λ[3,2] → X`, where the
     three `h..` are the SHARED-EDGE COMPATIBILITIES the constructor demands:
        edge (2,3): d₀α = g = d₀ s₀ g            (δ_comp_σ_self)
        edge (1,2): d₂α = 1ₓ = d₀ s₀(s₀ x)       (δ_comp_σ_self)
        edge (0,2): d₂ s₀ g = s₀ x = d₁ s₀(s₀ x) (δ_comp_σ_succ);
  3. `hornFilling` fills it (inner since 0 < 2 < 3) — the filler is obtained by
     `Classical.choose`, hence noncomputable;
  4. `yonedaEquiv` brings the filler back to an element `W ∈ X₃`, and `hd0/hd1/hd3`
     recover its three known faces;
  5. BOUNDARY READBACK: the faces of `τ = d₂ W` are computed from those of `W`
     using `dᵢ dⱼ = dⱼ₋₁ dᵢ` (`δ_comp_δ_apply`):
        d₀τ = d₀ d₂ W = d₁ d₀ W = d₁α = f
        d₁τ = d₁ d₂ W = d₁ d₁ W = d₁ s₀ g = g
        d₂τ = d₂ d₂ W = d₂ d₃ W = d₂ s₀(s₀ x) = 1ₓ
     i.e. `τ` witnesses `g ∼ f`. -/
lemma Homotopic.symm {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌}
    {f g : Edge X x y} (h : Homotopic f g) : Homotopic g f := by
  obtain ⟨α, h0, h1, h2⟩ := h
  -- (1) the three prescribed faces, pushed into the MAP picture:
  let f₀ := SSet.yonedaEquiv.symm α
  let f₁ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 0 g.val)
  let f₃ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 0 (idEdge X x).val)
  -- (2) shared-edge compatibilities for Λ[3,2]:
  have h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    have h_gt := SimplicialObject.δ_comp_σ_of_gt X (j := (0 : Fin 1)) (i := (1 : Fin 2)) (by decide)
    have h_gt' := types_congr_hom h_gt g.val
    have h_succ := SimplicialObject.δ_comp_σ_succ X (i := (0 : Fin 2))
    have h_succ' := types_congr_hom h_succ (idEdge X x).val
    dsimp at h_gt' h_succ'
    rw [h_gt', g.src]
    exact h_succ'.symm
  have h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h2]
    have h_self := SimplicialObject.δ_comp_σ_self X (i := (0 : Fin 2))
    have h_self' := types_congr_hom h_self (idEdge X x).val
    exact h_self'.symm
  have h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h0]
    have h_self := SimplicialObject.δ_comp_σ_self X (i := (0 : Fin 2))
    have h_self' := types_congr_hom h_self g.val
    exact h_self'.symm
  -- (3) fill the inner horn Λ[3,2] (the two `by decide`s discharge 0 < 2 and 2 < 3):
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (2 : Fin 4)) (by decide) (by decide) (horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)
  -- (4) the filler, back in the ELEMENT picture, with its three prescribed faces:
  let W := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 W = α := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₂.ι₀ ≫ horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ := by
      rw [← SSet.horn.ι_ι 2 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv α
  have hd1 : SimplicialObject.δ X 1 W = SimplicialObject.σ X 0 g.val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 1 ≫ Ω_hom = horn₃₂.ι₁ ≫ horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ := by
      rw [← SSet.horn.ι_ι 2 1 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₁_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 0 g.val)
  have hd3 : SimplicialObject.δ X 3 W = SimplicialObject.σ X 0 (idEdge X x).val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₂.ι₃ ≫ horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ := by
      rw [← SSet.horn.ι_ι 2 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 0 (idEdge X x).val)
  -- (5) the MISSING face is the witness; verify its boundary by readback:
  let τ := SimplicialObject.δ X 2 W
  refine ⟨τ, ?_, ?_, ?_⟩
  · -- d_0 τ = f.val
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd0, h1]
  · -- d_1 τ = g.val
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd1]
    have h_succ := SimplicialObject.δ_comp_σ_succ X (i := (0 : Fin 2))
    have h_succ' := types_congr_hom h_succ g.val
    exact h_succ'
  · -- d_2 τ = 1_x
    have h_rel := SSet.δ_comp_δ_apply (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide) W
    dsimp at h_rel
    change SimplicialObject.δ X 2 τ = (idEdge X x).val
    rw [← h_rel, hd3]
    have h_gt := SimplicialObject.δ_comp_σ_of_gt X (j := (0 : Fin 1)) (i := (1 : Fin 2)) (by decide)
    have h_gt' := types_congr_hom h_gt (idEdge X x).val
    dsimp at h_gt'
    rw [h_gt', (idEdge X x).src]
    rfl

/-- Transitivity (Lemma 7.4) — the same SANDWICH as symmetry, with a different
horn.  Given `α : f ∼ g` and `β : g ∼ h`, fill the inner horn `Λ[3,1]` with faces
      d₀ = β,      d₂ = α,      d₃ = s₀(s₀ x),
inner because `0 < 1 < 3`, and read the missing face `ω = d₁Ω` as a homotopy
`f ∼ h`.  The boundary readback gives `d₀ω = h`, `d₁ω = f`, `d₂ω = 1ₓ`.  The only
differences from `Homotopic.symm` are: `horn₃₁` (not `horn₃₂`), horn index `1`,
and which faces are prescribed vs. extracted. -/
lemma Homotopic.trans {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌}
    {f g h : Edge X x y} (hfg : Homotopic f g) (hgh : Homotopic g h) : Homotopic f h := by
  obtain ⟨α, h0α, h1α, h2α⟩ := hfg
  obtain ⟨β, h0β, h1β, h2β⟩ := hgh
  let f₀ := SSet.yonedaEquiv.symm β
  let f₂ := SSet.yonedaEquiv.symm α
  let f₃ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 0 (idEdge X x).val)
  have h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h2β]
    have h_self := SimplicialObject.δ_comp_σ_self X (i := (0 : Fin 2))
    have h_self' := types_congr_hom h_self (idEdge X x).val
    exact h_self'.symm
  have h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h1β, h0α]
  have h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h2α]
    have h_gt := SimplicialObject.δ_comp_σ_of_gt X (j := (0 : Fin 1)) (i := (1 : Fin 2)) (by decide)
    have h_gt' := types_congr_hom h_gt (idEdge X x).val
    dsimp at h_gt'
    rw [h_gt', (idEdge X x).src]
    rfl
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (1 : Fin 4)) (by decide) (by decide) (horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)
  let W := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 W = β := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₁.ι₀ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv β
  have hd2 : SimplicialObject.δ X 2 W = α := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 2 ≫ Ω_hom = horn₃₁.ι₂ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 2 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₂_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv α
  have hd3 : SimplicialObject.δ X 3 W = SimplicialObject.σ X 0 (idEdge X x).val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₁.ι₃ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 0 (idEdge X x).val)
  let ω := SimplicialObject.δ X 1 W
  refine ⟨ω, ?_, ?_, ?_⟩
  · -- d_0 ω = h.val
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd0, h0β]
  · -- d_1 ω = f.val
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [← h_rel, hd2, h1α]
  · -- d_2 ω = 1_x
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) W
    dsimp at h_rel
    change SimplicialObject.δ X 2 ω = (idEdge X x).val
    rw [← h_rel, hd3]
    have h_succ := SimplicialObject.δ_comp_σ_succ X (i := (0 : Fin 2))
    have h_succ' := types_congr_hom h_succ (idEdge X x).val
    exact h_succ'

/-- Theorem 7.5, packaged.  A `Setoid` bundles a relation with a proof that it is
an equivalence relation.  Declaring it an `instance` means Lean will, from now on,
automatically find this equivalence relation on `Edge X x y` — which is precisely
what is needed to form the quotient hom-sets `Edge X x y / ∼` in File 2. -/
instance homotopySetoid {X : SSet} [X.Quasicategory] (x y : X _⦋0⦌) :
    Setoid (Edge X x y) where
  r     := Homotopic
  iseqv := ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩
