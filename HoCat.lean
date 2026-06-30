import HoCat.HomotopyRelation

open Simplicial
open CategoryTheory
open SSet

universe u

/-!
================================================================================
FILE 2 of 3 — HoCat.lean
================================================================================

Mathematical goal.  Assemble the homotopy category `hX` of a quasi-category `X`
and prove it satisfies the category axioms (Theorem I).  Objects are vertices;
morphisms are homotopy classes of edges.  This realizes §§7–9 of
`source_target_shape_calculus.md` together with the two congruence lemmas
("Lemma A / Lemma B") and the unit and associativity laws.

The work splits into:
  • composition on REPRESENTATIVES (`compRep`), built by filling a Λ[2,1] horn;
  • independence of the chosen filler (`filler_independence`, Theorem 9.1);
  • that composition respects ∼ in each variable (`compRep_congr_first`, `compRep_congr_second`), so it
    descends to classes (`compRep_compat` → `SSet.HoCat.comp`);
  • the unit and associativity laws;
  • the final `Category` instance.

Every nontrivial proof reuses the horn SANDWICH from File 1 (translate → fill →
read back).  Watch for `Classical.choose`: the quasi-category hypothesis only asserts
fillers EXIST, so choosing one is noncomputable — which is harmless precisely
because `filler_independence` shows the choice does not matter up to homotopy.
================================================================================
-/

/-- Objects of `hX` are the vertices of `X`.  We use a type SYNONYM (same data,
new name) so the category structure we are about to attach cannot clash with
anything already living on `X _⦋0⦌`. -/
def SSet.HoCat (X : SSet) := X _⦋0⦌

/-- An object of `hX` may be used wherever a vertex of `X` is expected: the coercion
is the identity, reflecting that `HoCat X` is a type synonym for `X _⦋0⦌`. -/
instance (X : SSet) : CoeSort (SSet.HoCat X) (X _⦋0⦌) := ⟨id⟩

/-- A morphism `x → y` in `hX` is a homotopy class of edges: an element of the
quotient `Edge X x y / ∼` (Def. 7.6).  `Quotient (homotopySetoid …)` is exactly
that quotient, using the `Setoid` from File 1. -/
def SSet.HoCat.Hom (X : SSet.{u}) [X.Quasicategory] (x y : SSet.HoCat X) : Type u :=
  Quotient (homotopySetoid (X := X) x y)

/-- Two edges with the same underlying 1-simplex are equal.  (The `src`/`tgt`
fields are proofs of equalities, hence unique by proof irrelevance, so the
1-simplex `val` determines the whole bundled `Edge`.)  A small utility used to
turn equalities of simplices into equalities of edges. -/
lemma Edge.ext {X : SSet} {x y : X _⦋0⦌} {e₁ e₂ : Edge X x y} (h : e₁.val = e₂.val) : e₁ = e₂ := by
  cases e₁
  cases e₂
  dsimp at h
  subst h
  rfl

/-- The composition filler for a composable pair `(f, g)` (Lemma 8.2).  The two
edges meeting at `y` form an inner horn `Λ[2,1]`; we fill it.  `Λ[2,1]` is a
PUSHOUT of its two edges along the shared vertex, so `horn₂₁.isPushout.desc`
builds the horn map from `f`, `g` plus the single compatibility `d₀f = y = d₁g`.
`Classical.choose` then extracts an actual filler from the mere existence
statement supplied by `hornFilling` — this is the (harmless) noncomputable
choice. -/
noncomputable def compRep_filler {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    (f : Edge X x y) (g : Edge X y z) : X _⦋2⦌ := by
  let f₀ := SSet.yonedaEquiv.symm f.val
  let f₂ := SSet.yonedaEquiv.symm g.val
  have h_compat : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 1 ≫ f₂ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [f.tgt, g.src]
  let σ₀ := horn₂₁.isPushout.desc f₀ f₂ h_compat
  have h_fill := SSet.Quasicategory.hornFilling (n := 2) (i := (1 : Fin 3)) (by decide) (by decide) σ₀
  exact SSet.yonedaEquiv (Classical.choose h_fill)

/-- The two defining faces of the filler: `d₂ = f` and `d₀ = g` (the inputs to the
horn).  This spec is the workhorse cited throughout the file — whenever a later
proof needs to know "what are the outer faces of the composition filler", it is
this lemma.  Its proof is a small instance of the readback: identify the horn's
prescribed faces using `horn₂₁.isPushout.inl_desc`/`inr_desc`. -/
lemma compRep_filler_spec {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    (f : Edge X x y) (g : Edge X y z) :
    SimplicialObject.δ X 2 (compRep_filler f g) = f.val ∧
    SimplicialObject.δ X 0 (compRep_filler f g) = g.val := by
  dsimp [compRep_filler]
  generalize_proofs h_compat h_fill
  let σ_hom := Classical.choose h_fill
  have hσ := Classical.choose_spec h_fill
  let W := SSet.yonedaEquiv σ_hom
  constructor
  · rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 2 ≫ σ_hom = horn₂₁.ι₀₁ ≫ horn₂₁.isPushout.desc _ _ h_compat := by
      rw [← SSet.horn.ι_ι 1 2 (by decide), Category.assoc, ← hσ]
    rw [h_comp, horn₂₁.isPushout.inl_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv f.val
  · rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ σ_hom = horn₂₁.ι₁₂ ≫ horn₂₁.isPushout.desc _ _ h_compat := by
      rw [← SSet.horn.ι_ι 1 0 (by decide), Category.assoc, ← hσ]
    rw [h_comp, horn₂₁.isPushout.inr_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv g.val

/-- The composite REPRESENTATIVE "`g ∘ f` determined by the filler" is the middle
face `d₁` of the filler (Def. 8.1).  The `src`/`tgt` fields prove its endpoints
are `x` and `z` (Lemma 8.3), via the simplicial identity `dᵢ dⱼ = dⱼ₋₁ dᵢ`.  This
is only a representative; well-definedness on classes is established later. -/
noncomputable def compRep {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    (f : Edge X x y) (g : Edge X y z) : Edge X x z where
  val := SimplicialObject.δ X 1 (compRep_filler f g)
  src := by
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide) (compRep_filler f g)
    dsimp at h_rel
    rw [← h_rel, (compRep_filler_spec f g).1, f.src]
  tgt := by
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide) (compRep_filler f g)
    dsimp at h_rel
    rw [h_rel, (compRep_filler_spec f g).2, g.tgt]

/-- Filler independence (Theorem 9.1): any two fillers `σ, τ` of the SAME pair
`(f, g)` have homotopic middle faces `d₁σ ∼ d₁τ`.  Hence the class `⟦d₁σ⟧` depends
only on `f, g`, and the tentative definition `[g]∘[f] := [d₁σ]` is unambiguous in
the choice of filler.  Same `Λ[3,2]` horn SANDWICH as `Homotopic.symm`, with
prescribed faces `d₀ = τ`, `d₁ = σ`, `d₃ = s₀ f` and the homotopy extracted as the
missing face `d₂`.  This lemma is reused below (in `compRep_congr_second` and `associativity`)
to normalize an ad hoc 2-simplex back onto the canonical composite. -/
lemma filler_independence {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    (f : Edge X x y) (g : Edge X y z) (σ τ : X _⦋2⦌)
    (hσ2 : SimplicialObject.δ X 2 σ = f.val) (hσ0 : SimplicialObject.δ X 0 σ = g.val)
    (hτ2 : SimplicialObject.δ X 2 τ = f.val) (hτ0 : SimplicialObject.δ X 0 τ = g.val) :
    Homotopic
      (Edge.mk (SimplicialObject.δ X 1 σ)
        (by
          have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide) σ
          dsimp at h_rel
          rw [← h_rel, hσ2, f.src])
        (by
          have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide) σ
          dsimp at h_rel
          rw [h_rel, hσ0, g.tgt]))
      (Edge.mk (SimplicialObject.δ X 1 τ)
        (by
          have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 2)) (j := (1 : Fin 2)) (by decide) τ
          dsimp at h_rel
          rw [← h_rel, hτ2, f.src])
        (by
          have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide) τ
          dsimp at h_rel
          rw [h_rel, hτ0, g.tgt])) := by
  let f₀ := SSet.yonedaEquiv.symm τ
  let f₁ := SSet.yonedaEquiv.symm σ
  let f₃ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 0 f.val)
  have h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [hσ2]
    have h_succ := SimplicialObject.δ_comp_σ_succ X (i := (0 : Fin 2))
    have h_succ' := types_congr_hom h_succ f.val
    exact h_succ'.symm
  have h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [hτ2]
    have h_self := SimplicialObject.δ_comp_σ_self X (i := (0 : Fin 2))
    have h_self' := types_congr_hom h_self f.val
    exact h_self'.symm
  have h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [hτ0, hσ0]
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (2 : Fin 4)) (by decide) (by decide) (horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)
  let W := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 W = τ := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₂.ι₀ ≫ horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ := by
      rw [← SSet.horn.ι_ι 2 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv τ
  have hd1 : SimplicialObject.δ X 1 W = σ := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 1 ≫ Ω_hom = horn₃₂.ι₁ ≫ horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ := by
      rw [← SSet.horn.ι_ι 2 1 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₁_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv σ
  have hd3 : SimplicialObject.δ X 3 W = SimplicialObject.σ X 0 f.val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₂.ι₃ ≫ horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ := by
      rw [← SSet.horn.ι_ι 2 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 0 f.val)
  let ρ := SimplicialObject.δ X 2 W
  refine ⟨ρ, ?_, ?_, ?_⟩
  · -- d_0 ρ = d_1 τ
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd0]
  · -- d_1 ρ = d_1 σ
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd1]
  · -- d_2 ρ = 1_x
    have h_rel := SSet.δ_comp_δ_apply (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide) W
    dsimp at h_rel
    change SimplicialObject.δ X 2 ρ = (idEdge X x).val
    rw [← h_rel, hd3]
    have h_gt := SimplicialObject.δ_comp_σ_of_gt X (j := (0 : Fin 1)) (i := (1 : Fin 2)) (by decide)
    have h_gt' := types_congr_hom h_gt f.val
    dsimp at h_gt'
    rw [h_gt', f.src]
    rfl

/-- Lemma A (right congruence, §9): if `f ∼ f'` then `g∘f ∼ g∘f'`.  A `Λ[3,2]`
horn whose prescribed faces are the two composition fillers of `(f,g)` and
`(f',g)` together with the given homotopy `α : f ∼ f'`; the homotopy between the
composites is the extracted face. -/
lemma compRep_congr_first {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    {f f' : Edge X x y} (hff' : Homotopic f f') (g : Edge X y z) :
    Homotopic (compRep f g) (compRep f' g) := by
  obtain ⟨α, h0α, h1α, h2α⟩ := hff'
  let f₀ := SSet.yonedaEquiv.symm (compRep_filler f' g)
  let f₁ := SSet.yonedaEquiv.symm (compRep_filler f g)
  let f₃ := SSet.yonedaEquiv.symm α
  have h₀₁ : stdSimplex.δ 0 ≫ f₁ = stdSimplex.δ 0 ≫ f₀ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [(compRep_filler_spec f g).2, (compRep_filler_spec f' g).2]
  have h₀₃ : stdSimplex.δ 0 ≫ f₃ = stdSimplex.δ 2 ≫ f₀ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h0α, (compRep_filler_spec f' g).1]
  have h₁₃ : stdSimplex.δ 1 ≫ f₃ = stdSimplex.δ 2 ≫ f₁ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h1α, (compRep_filler_spec f g).1]
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (2 : Fin 4)) (by decide) (by decide) (horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm)
  let W := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 W = compRep_filler f' g := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₂.ι₀ ≫ horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm := by
      rw [← SSet.horn.ι_ι 2 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (compRep_filler f' g)
  have hd1 : SimplicialObject.δ X 1 W = compRep_filler f g := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 1 ≫ Ω_hom = horn₃₂.ι₁ ≫ horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm := by
      rw [← SSet.horn.ι_ι 2 1 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₁_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (compRep_filler f g)
  have hd3 : SimplicialObject.δ X 3 W = α := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₂.ι₃ ≫ horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm := by
      rw [← SSet.horn.ι_ι 2 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv α
  let τ := SimplicialObject.δ X 2 W
  refine ⟨τ, ?_, ?_, ?_⟩
  · -- d_0 τ = (compRep f' g).val
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd0]
    rfl
  · -- d_1 τ = (compRep f g).val
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd1]
    rfl
  · -- d_2 τ = 1_x
    have h_rel := SSet.δ_comp_δ_apply (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide) W
    dsimp at h_rel
    change SimplicialObject.δ X 2 τ = (idEdge X x).val
    rw [← h_rel, hd3, h2α]

/-- Lemma B (left congruence, §9): if `g ∼ g'` then `g∘f ∼ g'∘f`.  Subtler than
Lemma A: a `Λ[3,1]` horn threads a degeneracy `s₁ f` through the construction and
produces a 2-simplex `τ` that is a filler for `(f, g')` but not literally the
canonical one.  The final step calls `filler_independence f g' τ (compRep_filler
f g')` to identify `d₁τ` with the canonical composite `compRep f g'`, then chains.
This "build, then normalize via Theorem 9.1" move is the formal counterpart of the
drafts' remark that A, B and 9.1 share one horn pattern with permuted faces. -/
lemma compRep_congr_second {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    (f : Edge X x y) {g g' : Edge X y z} (hgg' : Homotopic g g') :
    Homotopic (compRep f g) (compRep f g') := by
  obtain ⟨β, h0β, h1β, h2β⟩ := hgg'
  let f₀ := SSet.yonedaEquiv.symm β
  let f₂ := SSet.yonedaEquiv.symm (compRep_filler f g)
  let f₃ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 1 f.val)
  have h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h2β]
    have h_le := SimplicialObject.δ_comp_σ_of_le X (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide)
    have h_le' := types_congr_hom h_le f.val
    dsimp at h_le'
    rw [h_le', f.tgt]
    rfl
  have h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [h1β, (compRep_filler_spec f g).2]
  have h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [(compRep_filler_spec f g).1]
    have h_succ := SimplicialObject.δ_comp_σ_succ X (i := (1 : Fin 2))
    have h_succ' := types_congr_hom h_succ f.val
    exact h_succ'.symm
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (1 : Fin 4)) (by decide) (by decide) (horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)
  let W := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 W = β := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₁.ι₀ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv β
  have hd2 : SimplicialObject.δ X 2 W = compRep_filler f g := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 2 ≫ Ω_hom = horn₃₁.ι₂ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 2 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₂_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (compRep_filler f g)
  have hd3 : SimplicialObject.δ X 3 W = SimplicialObject.σ X 1 f.val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₁.ι₃ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 1 f.val)
  let τ := SimplicialObject.δ X 1 W
  have hτ2 : SimplicialObject.δ X 2 τ = f.val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [← h_rel, hd3]
    exact δ_comp_σ_self_apply (1 : Fin 2) f.val
  have hτ0 : SimplicialObject.δ X 0 τ = g'.val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [h_rel, hd0, h0β]
  have h_comp_f_g : SimplicialObject.δ X 1 τ = (compRep f g).val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) W
    dsimp at h_rel
    rw [← h_rel, hd2]
    rfl
  have h_spec' := compRep_filler_spec f g'
  have h_ind := filler_independence f g' τ (compRep_filler f g') hτ2 hτ0 h_spec'.1 h_spec'.2
  obtain ⟨σ_witness, hσ0, hσ1, hσ2⟩ := h_ind
  refine ⟨σ_witness, hσ0, hσ1.trans h_comp_f_g, hσ2⟩

/-- Composition respects ∼ in BOTH variables at once: `g∘f ∼ g'∘f'`.  Two steps
chained by transitivity — change `f→f'` (Lemma A), then `g→g'` (Lemma B) — i.e.
`g∘f ∼ g∘f' ∼ g'∘f'`.  This is the compatibility datum that lets composition
descend to the quotient. -/
lemma compRep_compat {X : SSet} [X.Quasicategory] {x y z : X _⦋0⦌}
    (f f' : Edge X x y) (g g' : Edge X y z)
    (hf : Homotopic f f') (hg : Homotopic g g') :
    Homotopic (compRep f g) (compRep f' g') :=
  Homotopic.trans (compRep_congr_first hf g) (compRep_congr_second f' hg)

/-- Composition in `hX`, defined on classes.  `Quotient.lift₂` is the universal
property of the quotient in two variables: to define a map out of
`(Edge/∼) × (Edge/∼)`, give a map on representatives (`⟦compRep f g⟧`) PLUS a proof
it respects ∼ — which is `compRep_compat`, fed through `Quotient.sound` (the bridge
turning a `Homotopic` witness into an equality of classes).  This is where the two
congruence lemmas are actually used. -/
noncomputable def SSet.HoCat.comp {X : SSet} [X.Quasicategory] {x y z : SSet.HoCat X} :
    SSet.HoCat.Hom X x y → SSet.HoCat.Hom X y z → SSet.HoCat.Hom X x z :=
  fun fq gq =>
    Quotient.lift₂ (fun f g => Quotient.mk _ (compRep f g))
                   (fun f g f' g' hf hg => Quotient.sound (compRep_compat f f' g g' hf hg))
                   fq gq

/-- The identity morphism on `x` is the class of the identity edge `1ₓ`. -/
noncomputable def SSet.HoCat.id {X : SSet} [X.Quasicategory] (x : SSet.HoCat X) :
    SSet.HoCat.Hom X x x :=
  Quotient.mk _ (idEdge X x)

/-- Left unit law `[1ₓ] ∘ [f] = [f]`.  A small gem requiring NO horn: the
composition filler for `(1ₓ, f)` already IS a homotopy `compRep(1ₓ,f) ∼ f`.
Indeed by `compRep_filler_spec` it has `d₀ = f` and `d₂ = 1ₓ`, and by definition
`d₁ = compRep(1ₓ,f)` — exactly the three faces of a homotopy witness.  So the
witness is the filler itself.  (`Quotient.inductionOn` reduces the class `fq` to a
representative `f`; `Quotient.sound` turns the homotopy into the needed equality.) -/
lemma leftUnit {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌} (fq : SSet.HoCat.Hom X x y) :
    SSet.HoCat.comp (SSet.HoCat.id x) fq = fq := by
  revert fq
  intro (fq : Quotient (homotopySetoid x y))
  refine Quotient.inductionOn fq ?_
  intro f
  change Quotient.mk _ (compRep (idEdge X x) f) = Quotient.mk _ f
  apply Quotient.sound
  let W := compRep_filler (idEdge X x) f
  refine ⟨W, (compRep_filler_spec (idEdge X x) f).2, rfl, (compRep_filler_spec (idEdge X x) f).1⟩

/-- Right unit law `[f] ∘ [1_y] = [f]`.  Unlike the left unit, the canonical
filler for `(f, 1_y)` is not directly a homotopy, so this DOES need a `Λ[3,2]`
horn: build a 3-simplex from the degeneracies `s₀ f`, `s₁ f` and the filler, read
the missing face, and finish with `Homotopic.symm` (as in Lemma B). -/
lemma rightUnit {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌} (fq : SSet.HoCat.Hom X x y) :
    SSet.HoCat.comp fq (SSet.HoCat.id y) = fq := by
  revert fq
  intro (fq : Quotient (homotopySetoid x y))
  refine Quotient.inductionOn fq ?_
  intro f
  change Quotient.mk _ (compRep f (idEdge X y)) = Quotient.mk _ f
  apply Quotient.sound
  let W := compRep_filler f (idEdge X y)
  let f₀ := SSet.yonedaEquiv.symm W
  let f₁ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 1 f.val)
  let f₃ := SSet.yonedaEquiv.symm (SimplicialObject.σ X 0 f.val)
  have h₀₁ : stdSimplex.δ 0 ≫ f₁ = stdSimplex.δ 0 ≫ f₀ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    change SimplicialObject.δ X (Fin.castSucc 0) (SimplicialObject.σ X (Fin.succ 0) f.val) = SimplicialObject.δ X 0 W
    rw [δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) f.val, f.tgt]
    exact (compRep_filler_spec f (idEdge X y)).2.symm
  have h₀₃ : stdSimplex.δ 0 ≫ f₃ = stdSimplex.δ 2 ≫ f₀ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    change SimplicialObject.δ X (Fin.castSucc 0) (SimplicialObject.σ X 0 f.val) = SimplicialObject.δ X 2 W
    rw [δ_comp_σ_self_apply (0 : Fin 2) f.val]
    exact (compRep_filler_spec f (idEdge X y)).1.symm
  have h₁₃ : stdSimplex.δ 1 ≫ f₃ = stdSimplex.δ 2 ≫ f₁ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    change SimplicialObject.δ X (Fin.succ 0) (SimplicialObject.σ X 0 f.val) = SimplicialObject.δ X (Fin.succ 1) (SimplicialObject.σ X 1 f.val)
    rw [δ_comp_σ_succ_apply (0 : Fin 2) f.val]
    exact (δ_comp_σ_succ_apply (1 : Fin 2) f.val).symm
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (2 : Fin 4)) (by decide) (by decide) (horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm)
  let Ω := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 Ω = W := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₂.ι₀ ≫ horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm := by
      rw [← SSet.horn.ι_ι 2 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv W
  have hd1 : SimplicialObject.δ X 1 Ω = SimplicialObject.σ X 1 f.val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 1 ≫ Ω_hom = horn₃₂.ι₁ ≫ horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm := by
      rw [← SSet.horn.ι_ι 2 1 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₁_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 1 f.val)
  have hd3 : SimplicialObject.δ X 3 Ω = SimplicialObject.σ X 0 f.val := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₂.ι₃ ≫ horn₃₂.desc f₀ f₁ f₃ h₁₃.symm h₀₃.symm h₀₁.symm := by
      rw [← SSet.horn.ι_ι 2 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₂.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (SimplicialObject.σ X 0 f.val)
  let τ := SimplicialObject.δ X 2 Ω
  have hτ0 : SimplicialObject.δ X 0 τ = (compRep f (idEdge X y)).val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) Ω
    dsimp at h_rel
    rw [h_rel, hd0]
    rfl
  have hτ1 : SimplicialObject.δ X 1 τ = f.val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) Ω
    dsimp at h_rel
    rw [h_rel, hd1]
    exact δ_comp_σ_self_apply (1 : Fin 2) f.val
  have hτ2 : SimplicialObject.δ X 2 τ = (idEdge X x).val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (2 : Fin 3)) (j := (2 : Fin 3)) (by decide) Ω
    dsimp at h_rel
    change SimplicialObject.δ X 2 τ = (idEdge X x).val
    rw [← h_rel, hd3]
    have h_gt := SimplicialObject.δ_comp_σ_of_gt X (j := (0 : Fin 1)) (i := (1 : Fin 2)) (by decide)
    have h_gt' := types_congr_hom h_gt f.val
    dsimp
    dsimp at h_gt'
    change SimplicialObject.δ X 2 (SimplicialObject.σ X 0 f.val) = (idEdge X x).val
    rw [h_gt', f.src]
    rfl
  exact Homotopic.symm ⟨τ, hτ0, hτ1, hτ2⟩

/-- Associativity `([h]∘[g])∘[f] = [h]∘([g]∘[f])`.  After reducing all three
classes to representatives with `Quotient.inductionOn₃`, fill a `Λ[3,1]` horn whose
three prescribed faces are the composition fillers of `(g,h)`, `(f, g∘h)` and
`(f,g)`.  The face `d₁` of the filler is a 2-simplex exhibiting BOTH bracketings as
`d₁`-composites; a final `filler_independence` identifies it with the canonical
`compRep (compRep f g) h`.  This is the usual "both associated composites are faces
of one 3-simplex" argument. -/
lemma associativity {X : SSet} [X.Quasicategory] {x y z w : X _⦋0⦌}
    (fq : SSet.HoCat.Hom X x y) (gq : SSet.HoCat.Hom X y z) (hq : SSet.HoCat.Hom X z w) :
    SSet.HoCat.comp (SSet.HoCat.comp fq gq) hq = SSet.HoCat.comp fq (SSet.HoCat.comp gq hq) := by
  revert fq gq hq
  intro (fq : Quotient (homotopySetoid x y)) (gq : Quotient (homotopySetoid y z)) (hq : Quotient (homotopySetoid z w))
  refine Quotient.inductionOn₃ fq gq hq ?_
  intro f g h
  change Quotient.mk _ (compRep (compRep f g) h) = Quotient.mk _ (compRep f (compRep g h))
  apply Quotient.sound
  let f₀ := SSet.yonedaEquiv.symm (compRep_filler g h)
  let f₂ := SSet.yonedaEquiv.symm (compRep_filler f (compRep g h))
  let f₃ := SSet.yonedaEquiv.symm (compRep_filler f g)
  have h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [(compRep_filler_spec g h).1, (compRep_filler_spec f g).2]
  have h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    exact (compRep_filler_spec f (compRep g h)).2.symm
  have h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃ := by
    rw [δ_comp_yonedaEquiv_symm, δ_comp_yonedaEquiv_symm]
    congr 1
    rw [(compRep_filler_spec f (compRep g h)).1, (compRep_filler_spec f g).1]
  obtain ⟨Ω_hom, hΩ⟩ := SSet.Quasicategory.hornFilling (n := 3) (i := (1 : Fin 4)) (by decide) (by decide) (horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)
  let Ω := SSet.yonedaEquiv Ω_hom
  have hd0 : SimplicialObject.δ X 0 Ω = compRep_filler g h := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 0 ≫ Ω_hom = horn₃₁.ι₀ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 0 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₀_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (compRep_filler g h)
  have hd2 : SimplicialObject.δ X 2 Ω = compRep_filler f (compRep g h) := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 2 ≫ Ω_hom = horn₃₁.ι₂ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 2 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₂_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (compRep_filler f (compRep g h))
  have hd3 : SimplicialObject.δ X 3 Ω = compRep_filler f g := by
    rw [← yonedaEquiv_δ_comp]
    have h_comp : stdSimplex.δ 3 ≫ Ω_hom = horn₃₁.ι₃ ≫ horn₃₁.desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ := by
      rw [← SSet.horn.ι_ι 1 3 (by decide), Category.assoc, ← hΩ]
    rw [h_comp, SSet.horn₃₁.ι₃_desc]
    exact Equiv.apply_symm_apply SSet.yonedaEquiv (compRep_filler f g)
  let τ := SimplicialObject.δ X 1 Ω
  have hτ2 : SimplicialObject.δ X 2 τ = (compRep f g).val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) Ω
    dsimp at h_rel
    rw [← h_rel, hd3]
    rfl
  have hτ0 : SimplicialObject.δ X 0 τ = h.val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide) Ω
    dsimp at h_rel
    rw [h_rel, hd0, (compRep_filler_spec g h).2]
  have hτ1 : SimplicialObject.δ X 1 τ = (compRep f (compRep g h)).val := by
    have h_rel := SSet.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (1 : Fin 3)) (by decide) Ω
    dsimp at h_rel
    rw [← h_rel, hd2]
    rfl
  have h_filler_spec := compRep_filler_spec (compRep f g) h
  have h_ind := filler_independence (compRep f g) h τ (compRep_filler (compRep f g) h) hτ2 hτ0 h_filler_spec.1 h_filler_spec.2
  obtain ⟨σ_witness, hσ0, hσ1, hσ2⟩ := h_ind.symm
  refine ⟨σ_witness, hσ0.trans hτ1, hσ1, hσ2⟩

/-- THEOREM I.  `hX` is a genuine category.  This `instance` assembles the pieces
into Mathlib's `Category` typeclass: hom-sets, identity, composition, and the
three laws just proved.  Being an `instance`, it lets any later development treat
`hX` as a category with no further ceremony (e.g. `inferInstance` succeeds).
Note `comp` uses Lean's diagrammatic order: `f ≫ g` applies `f` first. -/
noncomputable instance SSet.HoCat.instCategory (X : SSet.{u}) [X.Quasicategory] :
    Category.{u, u} (SSet.HoCat X) where
  Hom     := SSet.HoCat.Hom X
  id      := SSet.HoCat.id
  comp    := fun f g => SSet.HoCat.comp f g
  id_comp := leftUnit
  comp_id := rightUnit
  assoc   := associativity
