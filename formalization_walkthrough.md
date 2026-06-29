# A Walkthrough of the Lean Formalization: The Functorial Homotopy Category of a Quasi-Category

> **What this is (please read first).** This project is my attempt to learn Lean 4 and quasi-categories
> at the same time. These notes are archival; they document my thought process as I built the
> formalization. They exist for a few reasons: as a learning resource for me; as a reminder to my future
> self if I ever come back to this; and on the chance that another beginner finds them useful for their
> own learning.
>
> I am very new to all of this, which has a few consequences worth stating up front:
> - I welcome all criticism, questions, and corrections.
> - There are parts I do not yet understand well and am currently treating as black boxes.
> - Is this the most efficient treatment of the problem? Quite possibly not.
> - Where I did something in a roundabout way, it is usually because I did not find a better analogous
>   method, or simply did not think of one.
>
> So this is **not** a roadmap, and not a groundbreaking solution to anything. It is messy, because it
> is a record of learning new concepts (which, at least for me, is an inherently messy process). Read it
> in that spirit, and take the confident-sounding sentences as "this is what I believe right now," not
> "this is settled."

*Prerequisites: familiarity with basic category theory (functors, natural transformations, quotients,
and equivalences). No prior exposure to the Lean 4 proof assistant is assumed.*

*Where things stand as I write this: the notes track the tagged checkpoint `hocat-functorial-core-v0.1`
specifically: `hX` is constructed, shown functorial in simplicial maps, and ordinary categories are recovered from
their nerves naturally. `HoCat/README.md` in the Lean project has the at-a-glance theorem inventory.*

---

## Table of contents

0. [What is being proved](#0-what-is-being-proved)
1. [The mathematical setting: simplicial sets and quasi-categories](#1-the-mathematical-setting)
2. [Just enough Lean to read the files](#2-just-enough-lean)
3. [File 1 (`HomotopyRelation.lean`): edges and their homotopies](#3-file-1)
4. [File 2 (`HoCat.lean`): building the category](#4-file-2)
5. [File 3 (`NerveHomotopy.lean`): comparison with ordinary categories](#5-file-3)
6. [File 4 (`Functoriality.lean`): `X ↦ hX` as a functor](#6-file-4)
7. [File 5 (`NerveNaturality.lean`): naturality and equivalence preservation](#7-file-5)
8. [The checkpoint layer: `Examples`, `API`, `Tests`](#8-checkpoint-layer)
9. [Recurring proof patterns, distilled](#9-recurring-proof-patterns)
10. [Dictionary: results ↔ Lean names](#10-dictionary)

---

<a name="0-what-is-being-proved"></a>
## 0. What is being proved

There are four theorems, and everything in the development serves one of them.

> **Theorem I.** If `X` is a quasi-category, then its *homotopy category* `hX` (objects: the vertices
> of `X`; morphisms: the homotopy classes of edges) is a genuine category.

> **Theorem II.** For an ordinary category `C`, the homotopy category of its nerve recovers `C`:
> there is an equivalence of categories `h(N C) ≌ C`.

> **Theorem III.** The assignment `X ↦ hX` is a *functor*: a simplicial map `F : X ⟶ Y` induces a
> functor `hF : hX ⥤ hY`, with `h(𝟙_X) = 𝟭_{hX}` and `h(G ∘ F) = hG ∘ hF`.

> **Theorem IV.** The recovery of Theorem II is *natural* in `C`, and it preserves equivalences: if
> `F : C ⥤ D` is an equivalence of ordinary categories, then `h(N F)` is an equivalence.

Theorem I is the central construction. Theorem II is the sanity check that the construction is the
*right* one: the passage `category ↦ nerve ↦ homotopy category` is the identity up to equivalence.
Theorems III and IV upgrade this from a statement about individual objects to a *functorial* one:
`hX` is not merely a category attached to each `X`, but the value of a functor compatible, through
nerves, with ordinary category theory. Together they form a coherent unit, the "functorial core",
tagged in the repository as `hocat-functorial-core-v0.1`.

All four theorems are formalized with **no axioms beyond the three that all of Mathlib uses**
(`propext`, `Classical.choice`, `Quot.sound`) and with **no `sorry`** (Lean's placeholder for an
unfinished proof). In other words, the machine has checked every step.

The development is split across five modules; the dependency arrows show what builds on what:

```
HomotopyRelation        File 1  edges, edge homotopy, the equivalence relation
   ↓
HoCat                   File 2  the category hX
   ↓            ↘
NerveHomotopy   Functoriality   File 3 / File 4  h(N C) ≅ C   /   X ↦ hX on maps
   ↓            ↓
   └──→ NerveNaturality          File 5  naturality + equivalence preservation
            ↓
        Examples · API · Tests   the checkpoint layer (§8)
```

Note that **File 4 (`Functoriality`) depends only on the base construction (File 2)**, not on the
nerve recovery; functoriality of `X ↦ hX` is logically independent of the comparison with ordinary
categories. File 5 draws on both.

A word on how to read this. Scattered through the document are **note-to-self callouts** (marked *Note
to self*). I put them at the exact spots that tripped me up while learning, usually a piece of Lean
terminology, or a design choice whose reason was not obvious to me at first. They are the main reason
these notes might help another beginner: they record the questions I actually had, in the order I had
them, and the answers I eventually settled on. If you are new to Lean, slow down at those callouts; if
you are not, skip them.

---

<a name="1-the-mathematical-setting"></a>
## 1. The mathematical setting: simplicial sets and quasi-categories

This section is pure mathematics; no Lean yet.

### 1.1 Simplicial sets

A **simplicial set** `X` is a sequence of sets `X₀, X₁, X₂, …` (the **`n`-simplices**) together with
**face maps** `dᵢ : Xₙ → Xₙ₋₁` and **degeneracy maps** `sᵢ : Xₙ → Xₙ₊₁` (for `0 ≤ i ≤ n`) satisfying
the **simplicial identities**. The ones we actually use are

```
dᵢ dⱼ = dⱼ₋₁ dᵢ      (i < j)
dᵢ sⱼ = sⱼ₋₁ dᵢ      (i < j)
dᵢ sⱼ = id           (i = j  or  i = j+1)
dᵢ sⱼ = sⱼ dᵢ₋₁      (i > j+1)
```

Think of an `n`-simplex as a "labelled `n`-dimensional triangle": `dᵢ` deletes the `i`-th vertex
(restricting to the opposite face), and `sᵢ` inserts a degenerate (collapsed) copy of the `i`-th
vertex. Formally `X` is a functor `Δᵒᵖ → Set`, but you lose nothing by picturing the `dᵢ`, `sᵢ`.

A `0`-simplex is a **vertex**; a `1`-simplex is an **edge**. For an edge `f` we adopt the convention
(fixed once and for all, and matched throughout the code):

> `d₁(f)` is the **source** and `d₀(f)` is the **target**.

So `f : x → y` means `d₁ f = x` and `d₀ f = y`. The degenerate edge `s₀(x)` is the **identity edge**
`1ₓ : x → x` (indeed `d₁ s₀ x = d₀ s₀ x = x`).

### 1.2 Standard simplices, boundaries, horns

The **standard `n`-simplex** `Δ[n]` is the representable simplicial set; by the Yoneda lemma a map
`Δ[n] → X` is exactly the same thing as an `n`-simplex of `X`. This equivalence is the technical
linchpin of the whole formalization (it lets us turn "an element of `Xₙ`" into "a map out of `Δ[n]`"
and back), and in Lean it is called `yonedaEquiv`.

Inside `Δ[n]` live two important sub-objects:

- the **boundary** `∂Δ[n]`, the union of all `n+1` faces;
- the **`i`-th horn** `Λ[n,i]`, the union of all faces *except* the `i`-th.

A horn is "a simplex with one face (and its interior) removed". A horn `Λ[n,i] → X` is therefore a
compatible family of `n` faces with a gap; **filling** the horn means extending it to a full simplex
`Δ[n] → X`. The horn is **inner** when `0 < i < n`.

### 1.3 Quasi-categories

> A simplicial set `X` is a **quasi-category** if every **inner** horn has a filler.

This is the only hypothesis we ever use about `X`. Its force: any "incomplete" inner configuration of
simplices can be completed. Two consequences drive everything:

- **Composition exists.** Two composable edges `f : x → y`, `g : y → z` define an inner horn
  `Λ[2,1] → X` (the two outer edges of a triangle). A filler is a `2`-simplex `σ` whose third edge
  `d₁ σ` is "a composite `g ∘ f`". (We will take this as the definition of a composite.)
- **Composition is unique up to homotopy.** Different fillers give homotopic composites; this is the
  filler-independence result proved later.

The catch (and the reason `hX` is nontrivial to build) is that the filler is **not canonical**.
Composition is only well-defined after we pass to homotopy classes. So we must first define homotopy,
prove it is an equivalence relation, then prove composition descends to classes.

### 1.4 Homotopy of edges

> For parallel edges `f, g : x → y`, write `f ∼ g` if there is a `2`-simplex `σ` with
> `d₀ σ = g`, `d₁ σ = f`, `d₂ σ = 1ₓ`.

Picture a triangle with vertices `x, x, y`: the edge `d₂` from the first `x` to the second is the
identity, the edge `d₁` is `f`, the edge `d₀` is `g`. Such a `σ` is a "homotopy from `f` to `g`".
The first real theorem is that `∼` is an equivalence relation on the parallel edges from `x` to `y`:
reflexive, symmetric, transitive. Symmetry and transitivity are the first place the quasi-category
hypothesis is used, via `3`-dimensional horns.

That is the entire mathematical vocabulary needed. Everything below is bookkeeping with horns.

---

<a name="2-just-enough-lean"></a>
## 2. Just enough Lean to read the files

Lean is a *dependently typed proof assistant*. Three ideas suffice.

**(a) Everything is a typed term.** `t : T` reads "`t` has type `T`". Types include ordinary sets
(`X _⦋1⦌` is the type of `1`-simplices) but also **propositions**: in Lean a proposition `P` is itself a
type, and a *proof* of `P` is a term of type `P`. So "to prove `P`" literally means "to construct a term
of type `P`". (This "propositions as types" viewpoint is sometimes called the Curry–Howard
correspondence.) In practice it means a definition and a theorem are written with the same syntax; the
only difference is whether the type on the right is data or a proposition.

> *Note to self.* `Prop` is the type whose terms are propositions. A function that lands in `Prop` (like
> `Homotopic` further down) is what a mathematician would just call a *predicate* or a *relation*: you
> feed it the data and it hands back a statement (`f ∼ g`), not a number or a set. It took me an
> embarrassingly long time to be comfortable with "a proposition *is* a type" and "a proof *is* a term of
> that type". Once that clicked, the fact that `def`, `lemma`, and `theorem` are essentially the same
> keyword stopped being mysterious.

**(b) Building blocks.**

- `structure`: a *record*, a single package with named fields. Defining a `structure` is like saying
  "an object of this kind consists of the following pieces of data, bundled together". Our `Edge` will be
  a record whose pieces are an edge together with the proofs about its endpoints.
- `def`: introduces a definition (either data, or, when its stated type is a proposition, a named
  statement).
- `lemma` / `theorem`: a `def` whose type happens to be a proposition; the body is the proof.
- `instance`: registers a fact for Lean to find on its own, so you do not have to supply it by hand
  every time. This is how Lean knows "`hX` is a category" without being reminded (the same automatic
  look-up sits behind `Category`, `Setoid`, and similar).

> *Note to self.* The word "`structure`" misled me at first. I read it as "mathematical structure" in
> the loose sense. It is narrower: it is just the keyword for a *record type*, a named bundle of fields.
> When you see `structure Edge ... where`, read it as "an `Edge` is exactly the following data, packaged
> together", and nothing more.

**(c) Two proof styles.** A proof can be written as a *term* (an explicit formula) or built
interactively in *tactic mode*, opened by `by`. Tactics are commands that transform the current goal:

- `intro h`: assume a hypothesis;
- `exact e`: close the goal with the term `e`;
- `refine ⟨_, _, _⟩`: provide a structured term with holes `?_` to fill;
- `rw [h]`: rewrite using an equation `h` (replace left-hand side by right-hand side);
- `simp`: simplify using a collection of known simplification rules;
- `obtain ⟨a, b⟩ := h`: split an existential or a conjunction `h` into its parts.

Common Lean 4 notations used throughout the library:

| Lean Syntax | Mathematical Meaning |
|---|---|
| `X _⦋n⦌` | the set `Xₙ` of `n`-simplices |
| `SimplicialObject.δ X i` | the face map `dᵢ` |
| `SimplicialObject.σ X i` | the degeneracy `sᵢ` |
| `Δ[n]` | the standard simplex |
| `Λ[n, i]` | the horn |
| `f ≫ g` | composition in a category, **in diagrammatic order** (`f` then `g`) |
| `𝟙 x` | the identity morphism on `x` |
| `⟦f⟧` / `Quotient.mk _ f` | the equivalence class of `f` |
| `∃ σ, P σ` written `⟨w, pf⟩` | an existential, given by a witness `w` and a proof `pf` |

Note on definitional vs. propositional equality: in Lean an "iff that is obvious on paper" can still
require a named lemma, because the system distinguishes things that are *equal by definition* (accepted
silently) from things that are merely *provably equal* (which require an explicit proof). Much of the
bulk below is exactly this: supplying, by hand, equalities a human would call "clear".

---

<a name="3-file-1"></a>
## 3. File 1 (`HomotopyRelation.lean`): edges and their homotopies

**Goal of the file:** produce, for every quasi-category `X` and vertices `x, y`, a `Setoid` on the
edges `x → y`, i.e. an equivalence relation packaged so Lean can later quotient by it. This is the
formal content of the statement that homotopy of parallel edges is an equivalence relation.

### 3.1 The type of edges

```lean
structure Edge (X : SSet) (x y : X _⦋0⦌) where
  val  : X _⦋1⦌
  src  : SimplicialObject.δ X 1 val = x
  tgt  : SimplicialObject.δ X 0 val = y
```

An `Edge X x y` is a `1`-simplex `val` *bundled with* the two proofs that its source is `x` and its
target is `y`. This is the literal reading of `Edgeₓ(x,y) = { f ∈ X₁ : d₁f = x, d₀f = y }`, except that
in a proof assistant the side conditions travel *inside* the object, so that whenever you hold an edge
you also hold the evidence about its endpoints. The convention `d₁ = src`, `d₀ = tgt` is the one fixed
in §1.

> *Note to self.* Three things I kept conflating, finally untangled:
> - **`Edge X x y`** is a *type*, the type of all edges from `x` to `y`. It plays the role of the *set*
>   `{ f ∈ X₁ : d₁ f = x, d₀ f = y }`.
> - **"an edge"** is a *term* of that type, e.g. `f : Edge X x y`, one specific element of that set.
> - **`f.val`** is the bare underlying `1`-simplex (a term of `X _⦋1⦌`). The bundle `f` is *not* the same
>   object as the raw simplex `f.val`: `f` is "the simplex `f.val`, together with the certificate that its
>   endpoints are `x` and `y`", and `.val` is the projection that throws the certificate away and returns
>   the bare simplex.
>
> This is why, all over the code, you see `f.val` where you might have expected just `f`: a face map like
> `δ` operates on bare `1`-simplices, so it must be fed `f.val`, not the bundled `f`.

### 3.2 The identity edge

```lean
def idEdge (X : SSet) (x : X _⦋0⦌) : Edge X x x where
  val  := SimplicialObject.σ X 0 x
  src  := by ...
  tgt  := by ...
```

The identity at `x` is the degenerate edge `1ₓ = s₀ x`. The two `by …` blocks discharge `d₁ s₀ x = x`
and `d₀ s₀ x = x`. On paper these are instances of the simplicial identity `dᵢ sⱼ = id`. In Lean the
identities live in Mathlib as equalities of *maps* (`δ_comp_σ_self`, `δ_comp_σ_succ`); the helper
`types_congr_hom` evaluates such a map-equality at the point `x` to get the equality of *elements* we
need. This `map-level lemma → apply to a point → element-level equality` move recurs throughout: Mathlib
states each simplicial identity once, abstractly, and we instantiate it.

> *Note to self.* Why must `idEdge` be defined with those two proof-fields, instead of just "`val := s₀ x`"?
> Because of the bundling in §3.1: an `Edge X x x` is *not* a bare simplex, it is a simplex **plus**
> proofs that its two endpoints are `x`. So to hand back the identity edge I have to produce all three
> fields: the simplex `s₀ x`, a proof its source is `x`, and a proof its target is `x`. The two `by …`
> blocks *are* those endpoint proofs; if I omit them Lean rightly refuses, because the record is
> incomplete. The convenience of carrying evidence inside the object (§3.1) has a matching cost: you must
> supply that evidence every time you build one.
>
> A rule I set myself early and never regretted: never do `Fin` index arithmetic by hand; always cite
> the named simplicial identity. The hand computations look easy and go wrong constantly.

### 3.3 The homotopy relation

```lean
def Homotopic {X : SSet} [X.Quasicategory] {x y : X _⦋0⦌} (f g : Edge X x y) : Prop :=
  ∃ σ : X _⦋2⦌,
    SimplicialObject.δ X 0 σ = g.val ∧
    SimplicialObject.δ X 1 σ = f.val ∧
    SimplicialObject.δ X 2 σ = (idEdge X x).val
```

A direct transcription of the definition of homotopy: `f ∼ g` iff some `2`-simplex has faces `(g, f, 1ₓ)`.
The square brackets `[X.Quasicategory]` declare that `X` is assumed to be a quasi-category, specifically an
*instance hypothesis*, found automatically wherever needed. (`Homotopic` itself does not use the
hypothesis, but carrying it uniformly keeps the later lemmas honest.)

> *Note to self.* Why is `Edge` a `structure ... where` while `Homotopic` is a `def ... : Prop :=`?
> Because they produce different *kinds* of thing. `Edge X x y` packages **data** (a simplex and two
> proofs), so it is a `structure` (a record type). `Homotopic f g` is a **statement about** two edges, namely
> a proposition, so it is an ordinary definition whose declared type is `Prop`, with the statement itself
> written after the `:=`. The rule of thumb I use now: `structure ... where` means "here is the data of a
> new kind of object"; `def ... : Prop :=` means "here is the *name* of a statement". The `∃ σ, ...`
> after the `:=` is that statement: "there exists a 2-simplex `σ` with these three faces".
>
> Note again the three `.val`s: the faces `δ ... σ` are bare `1`-simplices, so we compare them against
> `g.val`, `f.val`, `(idEdge X x).val` (the underlying simplices), not against the bundled edges (§3.1).

### 3.4 Reflexivity (the canary)

```lean
lemma Homotopic.refl ... (f : Edge X x y) : Homotopic f f := by
  refine ⟨SimplicialObject.σ X 0 f.val, ?_, ?_, ?_⟩
  · ...   -- d₀ s₀ f = f
  · ...   -- d₁ s₀ f = f
  · ...   -- d₂ s₀ f = 1ₓ
```

Reflexivity needs **no horn filling**; the witness is the degenerate `2`-simplex `s₀(f)`. The three
bullets verify its faces. The first two are `dᵢ s₀ = id`; the third computes
`d₂ s₀ f = s₀ (d₁ f) = s₀ x = 1ₓ` using `dᵢ sⱼ = sⱼ dᵢ₋₁` (the case `i > j+1`) and then the source
equation `f.src`. I think of this lemma as the "canary": if the face/degeneracy index conventions are
even slightly off, this is the first place it breaks. It compiles, so the conventions are correct, and I
trusted all the later face computations on that basis.

### 3.5 The Yoneda bridge: translating between elements and maps

Symmetry and transitivity require two pivotal lemmas that reconcile the element and map viewpoints:

```lean
lemma yonedaEquiv_δ_comp ... :
    yonedaEquiv (stdSimplex.δ i ≫ g) = δ X i (yonedaEquiv g)
lemma δ_comp_yonedaEquiv_symm ... :
    stdSimplex.δ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (δ X i x)
```

Consider the following structural situation. We have two equivalent pictures of an `n`-simplex:

- **element picture:** a point of `X _⦋n⦌`, where faces are taken with `δ X i`;
- **map picture:** a morphism `Δ[n] → X`, where "taking the `i`-th face" means *precomposing* with
  the coface inclusion `stdSimplex.δ i : Δ[n-1] → Δ[n]`.

`yonedaEquiv` is the dictionary between them. These two lemmas say the dictionary **commutes with
taking faces**: "apply `δ` then translate" = "translate then precompose", and the symmetric statement
for the inverse dictionary. Why do we need both pictures? Because **Mathlib's tools for horns are stated
in the map picture** (a horn is a sub-*object*, and a map out of it is a morphism), whereas our edges and
homotopies are stated in the **element picture**. Every horn argument below is a sandwich:

1. translate the prescribed faces from elements to maps (`yonedaEquiv.symm`);
2. build the horn and fill it, working in the map picture where Mathlib's tools live;
3. translate the faces of the filler back to elements (`yonedaEquiv`) to read off the witness.

These two lemmas are what make steps 1 and 3 sound.

> *Note to self.* This element-vs-map friction was the single thing that slowed me down most. The honest
> summary: our objects naturally live as *elements* of `Xₙ`, but the horn-filling tools want *maps*
> `Δ[n] → X`, and Lean will not silently identify the two even though the Yoneda lemma says they are "the
> same". Pulling the translation out into these two reusable lemmas, once, is what made the later proofs
> tractable rather than a swamp of conversions.

### 3.6 Symmetry (the first horn argument)

`Homotopic.symm` is symmetry of the homotopy relation. The mathematics: given a homotopy `α` from `f`
to `g`, build a `3`-simplex by filling the inner horn `Λ[3,2]`, then read its missing face as a homotopy
from `g` to `f`. The three faces of the horn are:

```
d₀ = α            on face (1,2,3)
d₁ = s₀(g)        on face (0,2,3)
d₃ = s₀(s₀ x)     on face (0,1,2)
```

and checks three **compatibility conditions** (the prescribed faces must agree on the edges they
share). Filling is legitimate because `0 < 2 < 3` makes the horn inner. The Lean proof mirrors this
line by line:

```lean
obtain ⟨α, h0, h1, h2⟩ := h                       -- unpack the given homotopy
let f₀ := yonedaEquiv.symm α                       -- the three faces, in the MAP picture
let f₁ := yonedaEquiv.symm (σ X 0 g.val)
let f₃ := yonedaEquiv.symm (σ X 0 (idEdge X x).val)
have h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃ := by ...   -- the compatibilities
have h₁₂ : ...
have h₂₃ : ...
obtain ⟨Ω_hom, hΩ⟩ :=
  SSet.Quasicategory.hornFilling ... (horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)  -- fill the horn
let W := yonedaEquiv Ω_hom                          -- the filler, back in the element picture
have hd0 : δ X 0 W = α := by ...                     -- identify the three known faces of W
have hd1 : δ X 1 W = σ X 0 g.val := by ...
have hd3 : δ X 3 W = σ X 0 (idEdge X x).val := by ...
let τ := δ X 2 W                                     -- the FOURTH (missing) face is the witness
refine ⟨τ, ?_, ?_, ?_⟩                              -- prove τ is a homotopy g ∼ f
· ...   -- d₀ τ = f.val
· ...   -- d₁ τ = g.val
· ...   -- d₂ τ = 1ₓ
```

Three details worth seeing:

- **`horn₃₂.desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃`** is Mathlib's constructor "assemble a map `Λ[3,2] → X` out of
  its three faces, given the compatibility proofs". The three `h…` are exactly the three shared-edge
  conditions, each proved by translating to elements and applying a simplicial identity.
- **`hornFilling`** consumes the horn map and the (automatically checked) fact `0 < 2 < 3`, and returns
  a filler `Ω_hom : Δ[3] → X` together with `hΩ`, the proof that it restricts to the prescribed horn.
- **Reading off faces.** The lines `hd0, hd1, hd3` recover the three prescribed faces of the filler
  (using `hΩ` plus the computation rules `horn₃₂.ι₀_desc`, …). Then the *fourth* face `τ = d₂ W` is the
  output. Verifying `τ` is the desired homotopy uses the simplicial identity `dᵢ dⱼ = dⱼ₋₁ dᵢ`
  (in Lean, `δ_comp_δ_apply`) to express the faces of `τ = d₂ W` in terms of the already-known faces of
  `W`. This is precisely the "reading off the boundary" computation one does by hand in the paper proof.

So the formal proof and the paper proof are the *same proof*; Lean only forces us to name the
element↔map translations and the simplicial identities that a human performs silently.

### 3.7 Transitivity

`Homotopic.trans` (transitivity) is the identical pattern with a different horn: now we are given two
homotopies `α : f ∼ g` and `β : g ∼ h`, we fill the inner horn `Λ[3,1]` with faces
`d₀ = β`, `d₂ = α`, `d₃ = s₀(s₀ x)`, and read the missing face `d₁` as a homotopy `f ∼ h`. The horn is
inner because `0 < 1 < 3`. In code the only changes from symmetry are: `horn₃₁` in place of `horn₃₂`,
horn index `1` in place of `2`, and the matching shuffle of which faces are prescribed and which is
extracted.

### 3.8 Packaging the equivalence relation

```lean
instance homotopySetoid (x y : X _⦋0⦌) : Setoid (Edge X x y) where
  r     := Homotopic
  iseqv := ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩
```

A `Setoid` is Mathlib's bundle of "a relation together with a proof it is an equivalence relation".
Declaring it an `instance` means: from now on, whenever Lean sees the type `Edge X x y`, it *knows* it
carries this equivalence relation and can form the quotient automatically. This is the formal
endpoint of this file, and the input to File 2.

---

<a name="4-file-2"></a>
## 4. File 2 (`HoCat.lean`): building the category

**Goal:** define `hX` and prove it satisfies the category axioms: composition, the congruence lemmas
that make it well-defined on homotopy classes, and the identity and associativity laws.

### 4.1 Objects and morphisms

```lean
def SSet.HoCat (X : SSet) := X _⦋0⦌
def SSet.HoCat.Hom (X : SSet) [X.Quasicategory] (x y : SSet.HoCat X) : Type :=
  Quotient (homotopySetoid (X := X) x y)
```

Objects of `hX` are vertices, so `HoCat X` is *defined to be* the type of vertices (a "type synonym":
same data, new name, which keeps the category structure we are about to add from colliding with
anything already attached to `X _⦋0⦌`). A morphism `x → y` is an element of the **quotient** of edges
by homotopy: an equivalence class `⟦f⟧`. This is `Hom_{hX}(x,y) = Edgeₓ(x,y)/∼`.

### 4.2 Composition on representatives

Composition must first be defined on *edges*, then shown to respect `∼` so it descends to classes.

```lean
noncomputable def compRep_filler (f : Edge X x y) (g : Edge X y z) : X _⦋2⦌ := by
  ... horn₂₁.isPushout.desc f₀ f₂ h_compat ...
  ... SSet.Quasicategory.hornFilling ... σ₀ ...
  exact yonedaEquiv (Classical.choose h_fill)
```

Given composable `f, g`, we form the inner horn `Λ[2,1]` (the two edges `f` and `g` meeting at `y`)
and fill it. `horn₂₁.isPushout` records that `Λ[2,1]` is a *pushout* of its two edges along the shared
vertex, the precise universal property that lets us build the horn map from `f` and `g` plus the
single compatibility `d₀ f = y = d₁ g` (their endpoints match). Two things to flag:

- **`Classical.choose`.** The quasi-category axiom asserts a filler *exists* but provides no canonical
  one. `Classical.choose` extracts a witness from a mere existence statement, a non-constructive
  choice. This is why the definition is marked **`noncomputable`**: it does not compute, it chooses.
  The whole theory is built to be insensitive to *which* filler is chosen (that is filler-independence,
  §4.3), so the choice does no harm.

```lean
def compRep (f : Edge X x y) (g : Edge X y z) : Edge X x z where
  val := SimplicialObject.δ X 1 (compRep_filler f g)
  src := ...
  tgt := ...
```

The composite *representative* is the middle face `d₁` of the filler, the composite "`g ∘ f` determined
by `σ`". Its `src`/`tgt` fields prove the endpoints are right (`x` and `z`), again via
`dᵢ dⱼ = dⱼ₋₁ dᵢ`. A companion lemma `compRep_filler_spec` records the two
defining faces `d₂(filler) = f` and `d₀(filler) = g`; it is cited dozens of times downstream.

### 4.3 Filler independence

```lean
lemma filler_independence
    (f : Edge X x y) (g : Edge X y z) (σ τ : X _⦋2⦌)
    (hσ2 : δ X 2 σ = f.val) (hσ0 : δ X 0 σ = g.val)
    (hτ2 : δ X 2 τ = f.val) (hτ0 : δ X 0 τ = g.val) :
    Homotopic (Edge.mk (δ X 1 σ) ...) (Edge.mk (δ X 1 τ) ...) := ...
```

The statement: *any two fillers of the same pair give homotopic composites.* The proof is one more
`Λ[3,2]` horn argument (faces `d₀ = τ`, `d₁ = σ`, `d₃ = s₀ f`; missing face `d₂` is the homotopy), and
structurally identical to symmetry. Its role is conceptual: it shows the class `⟦d₁ σ⟧` depends only on
`f` and `g`, so the *tentative* definition `[g] ∘ [f] := [d₁ σ]` is unambiguous as far as the choice of
filler is concerned. (It does not yet handle changing `f`, `g` within their classes; that comes next.)

### 4.4 Congruence of composition: `compRep_congr_first` / `compRep_congr_second`

```lean
lemma compRep_congr_first  (hff' : Homotopic f f') (g : Edge X y z) :
    Homotopic (compRep f g) (compRep f' g)
lemma compRep_congr_second (f : Edge X x y) (hgg' : Homotopic g g') :
    Homotopic (compRep f g) (compRep f g')
```

These are the "right congruence" and "left congruence" laws; I refer to them informally as *Lemma A*
and *Lemma B*. (The Lean names were chosen to refer to the **first** and **second argument of
`compRep f g`**, rather
than the words "left"/"right", which categorical composition order can make ambiguous.) Together they
say composition is well-defined on classes in each variable separately. `compRep_congr_first` is again
a `Λ[3,2]` horn (the prescribed faces are now the *two composition fillers* together with the given
homotopy `α`, and the extracted face is the homotopy between composites). `compRep_congr_second` is a
`Λ[3,1]` horn; it is slightly subtler because it threads a degeneracy `s₁ f` through the construction
and then **invokes `filler_independence`** at the end to convert the simplex it produces into the
standard composite representative. This reuse (building a homotopy and then correcting it back onto the
canonical composite via filler-independence) reflects that the congruence lemmas and filler-independence
all share one horn pattern, with different face assignments.

### 4.5 From representatives to classes

```lean
lemma compRep_compat (f f' : Edge X x y) (g g' : Edge X y z)
    (hf : Homotopic f f') (hg : Homotopic g g') :
    Homotopic (compRep f g) (compRep f' g') :=
  Homotopic.trans (compRep_congr_first hf g) (compRep_congr_second f' hg)
```

One line: change `f` to `f'` (Lemma A), then `g` to `g'` (Lemma B), and chain by transitivity. This is
the two-step argument `g∘f ∼ g∘f' ∼ g'∘f'`.

```lean
noncomputable def SSet.HoCat.comp :
    SSet.HoCat.Hom X x y → SSet.HoCat.Hom X y z → SSet.HoCat.Hom X x z :=
  fun fq gq => Quotient.lift₂ (fun f g => ⟦compRep f g⟧)
                              (fun f g f' g' hf hg => Quotient.sound (compRep_compat f f' g g' hf hg))
                              fq gq
```

`Quotient.lift₂` is the universal property of quotients in two variables: to define a function out of
`(Edge/∼) × (Edge/∼)`, give a function on representatives (`⟦compRep f g⟧`) **plus** a proof it is
compatible with the relation (`compRep_compat`). `Quotient.sound` turns a `Homotopic` witness into the
equality of classes that `lift₂` demands. This is the formal mechanism behind "composition descends to
the quotient"; mathematically it is invisible, but it is exactly where the two congruence lemmas are
*used*.

```lean
noncomputable def SSet.HoCat.id (x : SSet.HoCat X) : SSet.HoCat.Hom X x x := ⟦idEdge X x⟧
```

The identity morphism is the class of the identity edge.

### 4.6 The category axioms

Three laws remain.

**Left unit** (`leftUnit`): `[1ₓ] ∘ [f] = [f]`. The proof is a small gem. Unfolding, we must show
`compRep (idEdge X x) f ∼ f`. But the *composition filler itself* already witnesses this: by
`compRep_filler_spec` it has `d₀ = f`, `d₂ = 1ₓ`, and by definition `d₁ = compRep(1ₓ, f)`, which is
exactly the data of a homotopy `compRep(1ₓ,f) ∼ f`. So:

```lean
refine ⟨W, (compRep_filler_spec (idEdge X x) f).2, rfl, (compRep_filler_spec (idEdge X x) f).1⟩
```

no horn needed. (Conceptually: the filler witnessing "this is a composite of `1ₓ` and `f`" is the same
triangle that witnesses "the composite is homotopic to `f`".)

**Right unit** (`rightUnit`): `[f] ∘ [1_y] = [f]`. This one *does* need a `Λ[3,2]` horn, because the
canonical filler for `(f, 1_y)` is not directly a homotopy; one builds a `3`-simplex out of the two
degeneracies `s₀ f`, `s₁ f` and the filler, then extracts and (as in Lemma B) cleans up with
`Homotopic.symm`.

**Associativity** (`associativity`): `([h]∘[g])∘[f] = [h]∘([g]∘[f])`. After reducing to
representatives with `Quotient.inductionOn₃` (the three-variable "it suffices to check on classes"
principle), one fills a `Λ[3,1]` horn whose three prescribed faces are the composition fillers of
`(g,h)`, `(f, compRep g h)`, and `(f,g)`. The face `d₁` of the filler is a `2`-simplex exhibiting
*both* bracketings as `d₁`-composites; a final appeal to `filler_independence` identifies it with the
canonical `compRep (compRep f g) h`. This is the standard "associativity pentagon collapses because all
the composites are faces of one `3`-simplex" argument, made formal.

```lean
noncomputable instance SSet.HoCat.instCategory (X : SSet) [X.Quasicategory] :
    Category (SSet.HoCat X) where
  Hom := SSet.HoCat.Hom X
  id := SSet.HoCat.id
  comp := fun f g => SSet.HoCat.comp f g
  id_comp := leftUnit
  comp_id := rightUnit
  assoc := associativity
```

This `instance` **is Theorem I.** It assembles the pieces into Mathlib's `Category` typeclass: hom-sets,
identities, composition, and the three laws. Because it is an `instance`, any later development can use
`hX` as a category with no further ceremony, e.g. the milestone `example : Category (SSet.HoCat X) :=
inferInstance` succeeds. Note `comp` follows Lean's diagrammatic order (`f ≫ g` means `f` first); the
this convention is an easy thing to get backwards, so the instance is written to match it.

---

<a name="5-file-3"></a>
## 5. File 3 (`NerveHomotopy.lean`): comparison with ordinary categories

**Goal:** prove `h(N C) ≌ C` (Theorem II). This is the promised compatibility check.

### 5.1 The nerve, and what Mathlib already gives us

The **nerve** `N C` of a category `C` is the simplicial set whose `n`-simplices are the chains of `n`
composable morphisms. Mathlib supplies everything we need about it and we do *not* reprove any of it:

- `CategoryTheory.Nerve.quasicategory`: the nerve is a quasi-category (so `h(N C)` is defined);
- `nerveEquiv : ComposableArrows C 0 ≃ C`: vertices of `N C` are objects of `C`;
- `nerve.homEquiv`: **edges of `N C` between vertices `x, y` correspond bijectively to morphisms
  `x → y` in `C`** (the defining feature of the nerve in dimension 1);
- `nerve.homEquiv_id`, `nerve.homEquiv_comp`: this bijection sends identity edges to identities and
  composition-fillers to actual composites.

This was a deliberate choice: lean on the nerve material Mathlib already provides rather than rebuild
it.

### 5.2 Edge translation

```lean
def toSSetEdge (e : Edge (nerve C) x y) : SSet.Edge (nerve C) x y := ...
def ofSSetEdge (e : SSet.Edge (nerve C) x y) : Edge (nerve C) x y := ...
```

A purely administrative pair: this project's `Edge` record (File 1) and Mathlib's own `SSet.Edge`
record carry the same data, so we convert back and forth. (These conversions are the one place where the
deliberate decision to keep `Edge` at the root namespace (rather than merge it into `SSet.Edge`) is
visible; mathematically the maps are identities.)

### 5.3 Homotopy in the nerve is equality

```lean
lemma nerve_homotopic_iff (f g : Edge (nerve C) x y) :
    Homotopic f g ↔ nerve.homEquiv (toSSetEdge f) = nerve.homEquiv (toSSetEdge g)
```

This is the mathematical heart of Theorem II: **two edges of `N C` are homotopic iff they are the same
morphism of `C`.** Forward direction: a homotopy `σ` is a `2`-simplex of `N C`, i.e. a commuting
triangle in `C` with one edge an identity; reading the triangle (via `homEquiv_comp` and `homEquiv_id`)
forces the two morphisms to be equal. Backward: if they are literally equal, reflexivity gives a
homotopy. Consequently the hom-sets of `h(N C)` and of `C` are in bijection: passing to homotopy
classes collapses nothing beyond honest equality.

### 5.4 The comparison functor

```lean
noncomputable def nerveHoCatFunctor (C : Type u) [Category.{v} C] :
    SSet.HoCat (nerve C) ⥤ C where
  obj := fun x => nerveEquiv x
  map := fun fq => Quotient.liftOn fq (fun f => nerve.homEquiv (toSSetEdge f)) (by ...)
  map_id := ...
  map_comp := ...
```

The functor `h(N C) → C` is the identity on objects (a vertex *is* an object) and sends a morphism
class `⟦f⟧` to the morphism `homEquiv f` of `C`. `Quotient.liftOn` is again "define a function on
classes by defining it on representatives and proving it respects the relation", and the proof that it
respects the relation is *exactly* `nerve_homotopic_iff` (homotopic edges give equal morphisms, so the
value is well-defined). `map_id` uses `homEquiv_id`; `map_comp` uses `homEquiv_comp` applied to the
composition filler. So functoriality of the comparison map is precisely the statement that `homEquiv`
respects identities and composites, which Mathlib already proved.

### 5.5 Why the equivalence is built from full + faithful + essentially surjective

To upgrade the functor to an equivalence, one *could* hand-build an inverse functor together with unit
and counit natural isomorphisms. The first version of this file did exactly that and ran into a
notorious obstacle: the objects of `h(N C)` are `ComposableArrows C 0` while the objects of `C` are
plain objects, related only by the *isomorphism* `nerveEquiv`, not by definitional equality. Naturality
squares then bristle with `eqToHom` ("transport along an equality of objects") terms, and the rewrites
needed to simplify them fail for subtle dependent-type reasons.

The robust fix is to invoke the classical criterion:

> A functor is an equivalence iff it is **faithful**, **full**, and **essentially surjective**.

and let Mathlib assemble the equivalence and all its coherence data internally. So the file proves three
instances:

```lean
instance : (nerveHoCatFunctor C).Faithful  where map_injective := ...    -- from nerve_homotopic_iff (⇐)
instance : (nerveHoCatFunctor C).Full      where map_surjective := ...   -- preimage via homEquiv.symm
instance : (nerveHoCatFunctor C).EssSurj   where mem_essImage  := ...    -- witness nerveEquiv.symm c
```

- **Faithful** (injective on morphisms): if `homEquiv f = homEquiv g` then `f ∼ g` then `⟦f⟧ = ⟦g⟧`.
  This is the `⇐` half of `nerve_homotopic_iff`.
- **Full** (surjective on morphisms): given a morphism `g : x → y` in `C`, the class
  `⟦homEquiv⁻¹ g⟧` maps to it. Crucially this uses `homEquiv.symm` directly and so needs **no
  `eqToHom`**, sidestepping the whole difficulty above.
- **Essentially surjective**: every object `c` of `C` is `nerveEquiv` of the vertex `nerveEquiv.symm c`,
  hence in the image up to (an `eqToIso`) isomorphism. Here a single harmless `eqToHom` survives, inside
  an *isomorphism* where it causes no trouble.

```lean
instance : (nerveHoCatFunctor C).IsEquivalence where
  faithful := ...; full := ...; essSurj := ...

noncomputable def nerveHoCatIso (C : Type u) [Category.{v} C] :
    SSet.HoCat (nerve C) ≌ C :=
  (nerveHoCatFunctor C).asEquivalence
```

`asEquivalence` is Mathlib's packaging of the criterion: from `IsEquivalence` it produces the genuine
equivalence `≌`, fabricating the inverse functor and the unit/counit isomorphisms for us. **This is
Theorem II.**

*Note to self.* The thing I want to remember from this file: *when an explicit construction drowns in
coherence bookkeeping (the `eqToHom` swamp), back off and characterize the object abstractly (here:
fully faithful + essentially surjective) and let the library build it.* The first version I wrote did
hand-roll the inverse functor and the unit/counit isomorphisms, and I got stuck on the naturality
squares; the fully-faithful route was both shorter and the thing I actually understood. Check later
whether this is the "right" general lesson or just what rescued me this time.

### 5.6 A note on universes

The signature `(C : Type u) [Category.{v} C]` uses two independent universe levels (`u` for the
objects, `v` for the morphisms), which is the standard, maximally general convention. (An earlier version
of this file tied them together as `Category.{u} C`; separating them costs nothing and makes the theorem
apply to,
e.g., large categories with small hom-sets.) The nerve of such a `C` lives in `SSet.{max u v}`, and the
category structure from File 2 specializes to it automatically, since File 1 and File 2 were written
polymorphically in the ambient simplicial set.

---

<a name="6-file-4"></a>
## 6. File 4 (`Functoriality.lean`): `X ↦ hX` as a functor

**Goal:** a simplicial map `F : X ⟶ Y` of quasi-categories induces a functor `hF : hX ⥤ hY`, and this
assignment respects identities and composition (Theorem III). The whole file rests on **File 2 only**;
it never mentions nerves. Functoriality of `X ↦ hX` is independent of the comparison with ordinary
categories.

The technical glue here differs from Files 1–3. There the hard part was the *Yoneda bridge* (element ↔
map). Here it is simply the **naturality of `F`**: as a natural transformation `X ⟶ Y`, `F` commutes
with every simplicial operator. Evaluated at a coface or codegeneracy this reads `F(dᵢ s) = dᵢ(F s)`
and `F(sᵢ s) = sᵢ(F s)`, i.e. *"pushing a simplex forward along `F` commutes with faces and degeneracies"*.
In Lean it is `F.naturality (…).op` applied to a point via `types_congr_hom`. Every boundary check in
the file is an instance of this one fact.

### 6.1 Mapping edges, identities, homotopies

```lean
def Edge.map (F : X ⟶ Y) (f : Edge X x y) : Edge Y (F.app _ x) (F.app _ y) where
  val := F.app _ f.val
  src := ...   -- d₁ (F f) = F (d₁ f) = F x,  by naturality at δ 1
  tgt := ...   -- d₀ (F f) = F (d₀ f) = F y,  by naturality at δ 0
```

`Edge.map F f` is just "apply `F` to the underlying `1`-simplex"; the endpoints follow by naturality.
`Edge.map_idEdge` (that `F(1ₓ) = 1_{Fx}`) is naturality at the degeneracy `σ 0`.

`Homotopic.map` then says **`F` preserves edge homotopy**: if `σ` witnesses `f ∼ g`, then `F σ`
witnesses `Ff ∼ Fg`. No horn is filled; `F σ` is already a `2`-simplex with the right faces (each
checked by naturality, the identity-edge face by `Edge.map_idEdge`). This is the conceptual point: a
simplicial map sends a homotopy witness *directly* to a homotopy witness.

### 6.2 Descent to homotopy classes

```lean
def SSet.HoCat.mapHom (F : X ⟶ Y) : HoCat.Hom X x y → HoCat.Hom Y (F.app _ x) (F.app _ y) :=
  fun q => Quotient.liftOn q (fun f => ⟦Edge.map F f⟧)
                             (fun f g hfg => Quotient.sound (Homotopic.map F hfg))
```

Because `F` preserves homotopy, `[f] ↦ [F f]` is well-defined on classes, and the same `Quotient.liftOn`
idiom as before, with `Homotopic.map` discharging respect-for-`∼`.

### 6.3 Compatibility with composition (the one real lemma)

```lean
lemma Edge.map_compRep_homotopic (F : X ⟶ Y) (f : Edge X x y) (g : Edge X y z) :
    Homotopic (Edge.map F (compRep f g)) (compRep (Edge.map F f) (Edge.map F g))
```

Here the non-canonical choice of fillers must be confronted. `compRep f g` is `d₁` of a *chosen* filler
`W` for `(f, g)`. Applying `F`, the simplex `F W` is a perfectly good filler for `(Ff, Fg)`: its outer
faces are `Ff` and `Fg` by naturality, but it need **not** be the filler chosen to define
`compRep (Ff) (Fg)`. The two are reconciled by **`filler_independence`** (§4.3): two fillers of
the same pair have homotopic middle edges. So the "build, then normalize via 9.1" move from File 2
reappears, but with a twist. **No new horn is constructed**; the second filler is handed to us for free
by pushing `W` forward along `F`. The lemma is, in a slogan: *the image of a filler is a filler.*

### 6.4 The induced functor and strict functoriality

```lean
def SSet.HoCat.map (F : X ⟶ Y) : SSet.HoCat X ⥤ SSet.HoCat Y where
  obj := fun x => F.app _ x
  map := SSet.HoCat.mapHom F
  map_id := ...      -- Edge.map_idEdge
  map_comp := ...    -- Edge.map_compRep_homotopic
```

and then functoriality of `X ↦ hX` itself:

```lean
theorem SSet.HoCat.map_id   : SSet.HoCat.map (𝟙 X) = 𝟭 (SSet.HoCat X)
theorem SSet.HoCat.map_comp : SSet.HoCat.map (F ≫ G) = SSet.HoCat.map F ⋙ SSet.HoCat.map G
```

These are **strict equalities of functors**, not merely natural isomorphisms, available because
`SSet.HoCat.map` is the identity on objects on the nose, so `Functor.ext` reduces them to the
objectwise/morphismwise `simp` lemmas (`map_id_obj`/`map_id_map`, `map_comp_obj`/`map_comp_map`). This
is **Theorem III**.

---

<a name="7-file-5"></a>
## 7. File 5 (`NerveNaturality.lean`): naturality and equivalence preservation

**Goal:** the comparison `h(N C) ⥤ C` of File 3 is natural in `C`, and carries equivalences of ordinary
categories to equivalences of homotopy categories (Theorem IV). This file uses both File 3 and File 4.

### 7.1 The nerve of a functor

A functor `F : C ⥤ D` induces a simplicial map `N F : N C ⟶ N D` (Mathlib's `nerveMap F`). Feeding it to
File 4 gives `h(N F) : h(N C) ⥤ h(N D)`. The question is how `h(N F)` interacts with the comparison
functors `h(N C) ⥤ C` and `h(N D) ⥤ D`.

### 7.2 The naturality square

```lean
theorem nerveHoCatFunctor_natural (F : C ⥤ D) :
    SSet.HoCat.map (nerveMap F) ⋙ nerveHoCatFunctor D = nerveHoCatFunctor C ⋙ F
```

In words: the two routes `h(N C) → D` agree. "Apply `h(N F)`, then compare with `D`" equals "compare
with `C`, then apply `F`". The morphism-level content is one lemma, `homEquiv_map_nerveMap`, saying the
edge-to-morphism dictionary `homEquiv` commutes with `N F`: reading off the morphism after pushing an
edge through `N F` is the same as applying `F` to the morphism you read off first. As in File 4, the
strict functor equality then follows by `Functor.ext`. This is **Theorem IV (naturality)**, upgrading
the objectwise `h(N C) ≅ C` to a statement about the *functor* `C ↦ h(N C)`.

### 7.3 Equivalence preservation

```lean
instance nerveHoCat_preserves_equivalence (F : C ⥤ D) [F.IsEquivalence] :
    (SSet.HoCat.map (nerveMap F)).IsEquivalence
```

If `F` is an equivalence, so is `h(N F)`. The proof is a clean instance of a new pattern: **transport a
property across a commuting square of functors whose verticals are equivalences.** Because
`nerveHoCatFunctor C` and `nerveHoCatFunctor D` are equivalences (File 3) and the square
`nerveHoCatFunctor_natural` commutes on the nose, faithfulness, fullness and essential surjectivity of
`F` transfer to `h(N F)` by composing and cancelling the (invertible) comparison functors. The three
criteria are bundled into `IsEquivalence`, exactly as in File 3. In short, `h` preserves equivalences,
here for the nerves of ordinary functors.

---

<a name="8-checkpoint-layer"></a>
## 8. The checkpoint layer: `Examples`, `API`, `Tests`

Three small files close the checkpoint; none introduces new mathematics.

- **`Examples.lean`**: sanity instances of the comparison (`h(N C) ≅ C` for an arbitrary category, a
  preorder, and a discrete category, plus a one-line check that `h(N F)` is an equivalence when `F` is).
  Deliberately modest; Čech nerves, finite spaces, and exit-path examples are deferred to a later phase.
- **`API.lean`**: thin, citable restatements of the main results under stable names
  (`homotopic_equivalence`, `comp_well_defined`, `HoCat_category`, `HoCat_functorial_on_maps`,
  `nerve_HoCat_equiv`). Each is `exact`-equal to an existing result; their job is to give later code a
  set of names to refer to that will not change when the internal proofs are reorganized. (I named the
  file `API.lean` simply because it collects those stable public-facing names in one place.)
- **`Tests.lean`**: compile-only regression checks pinning the *shapes* of the public-facing
  declarations (e.g. that `SSet.HoCat.map (F ≫ G) = SSet.HoCat.map F ⋙ SSet.HoCat.map G` typechecks). If
  a refactor changes a signature, the matching line stops compiling, a cheap tripwire. It is a separate
  build target, not
  imported by the aggregator.

---

<a name="9-recurring-proof-patterns"></a>
## 9. Recurring proof patterns, distilled

If I reread only one section later, it should be this one. Seven patterns ended up generating almost
every proof. The first five build the category (Files 1–3); the last two make it functorial (Files
4–5). Writing them down here so I don't have to rediscover them next time.

1. **The horn descent pattern** (symmetry, transitivity, filler independence, Lemma A, Lemma B, right
   unit, associativity, *seven* times total). To produce a `2`-simplex with prescribed boundary:
   *(i)* translate three known `2`-simplices to the map picture with `yonedaEquiv.symm`; *(ii)* assemble
   an inner horn `Λ[3,i]` from them via `horn₃ᵢ.desc`, supplying three shared-edge compatibilities;
   *(iii)* fill it with `Quasicategory.hornFilling`; *(iv)* translate the filler back with `yonedaEquiv`;
   *(v)* identify the three known faces and read the fourth as the output. This is the formal skeleton of
   every `3`-horn proof in Files 1–2.

2. **Element ↔ map translation.** Mathlib's horn tools speak of maps `Δ[n] → X`; our objects are
   elements of `X _⦋n⦌`. `yonedaEquiv` and the two bridge lemmas of §3.5 move between the two. Whenever
   you see `yonedaEquiv.symm` appear, a horn is about to be built; whenever you see `yonedaEquiv` after a
   `hornFilling`, faces are about to be read.

3. **Reading faces via the simplicial identities.** After extraction, faces of `dᵢ(filler)` are computed
   from faces of the filler using `dᵢ dⱼ = dⱼ₋₁ dᵢ` (`δ_comp_δ_apply`) and the degeneracy identities.
   No index is ever manipulated by hand; a *named* identity is always cited (the rule from §3.2).

4. **Quotients.** Three idioms: `Quotient.mk`/`⟦·⟧` forms a class; `Quotient.sound` turns a relation
   witness into an equality of classes; `Quotient.lift₂` / `liftOn` / `inductionOn(₂,₃)` define functions
   on, or reduce goals to, representatives. These are the formal shadow of "well-defined on
   equivalence classes" and "check on representatives".

5. **Retreat to a universal property.** When direct coherence (the unit/counit `eqToHom` swamp) becomes
   unmanageable, characterize the object abstractly (here: fully faithful + essentially surjective ⇒
   equivalence) and let the library build it.

6. **Pushforward along a simplicial map** (all of File 4). To move an edge, identity, homotopy, or
   filler along `F : X ⟶ Y`, apply `F` componentwise (`F.app`) and discharge every boundary condition
   by `F.naturality` at the relevant coface/codegeneracy. No horn is filled: the image of a witness is a
   witness, and the image of a filler is a filler; the only correction needed is to normalize the
   image filler back onto the *chosen* one via `filler_independence`. This is the functorial twin of the
   horn-descent pattern, with naturality of `F` playing the role the Yoneda bridge played in Files 1–3.

7. **Transport a property across a strict naturality square** (File 5). Given a commuting square of
   functors whose two verticals are equivalences, a property of one horizontal (faithful / full /
   essentially surjective) transfers to the other by composing and cancelling the verticals. This is how
   `h(N F)` inherits "equivalence" from `F`.

*Note to self.* The thing that surprised me: the *creative* mathematical content (which horn, which
faces, which compatibilities) turned out to be small, and to live almost entirely in the ordinary
mathematics I worked out by hand before touching Lean. The *bulk* of the Lean was administrative: the
translation between the element and map pictures, and the quotient bookkeeping, that informal
writing just elides. So formalization didn't make the mathematics harder for me; it made the silent
steps audible (and occasionally loud). Worth remembering when the next file feels like mostly plumbing;
that may be normal, not a sign I'm doing it wrong.

---

<a name="10-dictionary"></a>
## 10. Dictionary: results ↔ Lean names

| Result | Lean name | File |
|---|---|---|
| edges with fixed endpoints `Edgeₓ(x,y)` | `Edge` | 1 |
| the identity edge `1ₓ = s₀ x` | `idEdge` | 1 |
| homotopy of parallel edges | `Homotopic` | 1 |
| reflexivity | `Homotopic.refl` | 1 |
| symmetry (`Λ[3,2]` horn) | `Homotopic.symm` | 1 |
| transitivity (`Λ[3,1]` horn) | `Homotopic.trans` | 1 |
| `∼` is an equivalence relation | `homotopySetoid` | 1 |
| the Yoneda bridge (element ↔ map) | `yonedaEquiv_δ_comp`, `δ_comp_yonedaEquiv_symm` | 1 |
| morphisms `Hom_{hX}(x,y)` | `SSet.HoCat`, `SSet.HoCat.Hom` | 2 |
| composition filler exists (`Λ[2,1]` horn) | `compRep_filler` | 2 |
| composite representative | `compRep` (+ `compRep_filler_spec`) | 2 |
| filler independence (`Λ[3,2]` horn) | `filler_independence` | 2 |
| right congruence (Lemma A) | `compRep_congr_first` | 2 |
| left congruence (Lemma B) | `compRep_congr_second` | 2 |
| composition descends to classes | `compRep_compat`, `SSet.HoCat.comp` | 2 |
| identity, unit laws, associativity | `SSet.HoCat.id`, `leftUnit`, `rightUnit`, `associativity` | 2 |
| **Theorem I**: `hX` is a category | `SSet.HoCat.instCategory` | 2 |
| homotopy in `N C` = equality of morphisms | `nerve_homotopic_iff` | 3 |
| comparison functor `h(N C) → C` | `nerveHoCatFunctor` | 3 |
| fully faithful + essentially surjective | `…_faithful_inst`, `…_full`, `…_essSurj` | 3 |
| **Theorem II**: `h(N C) ≌ C` | `nerveHoCatIso` | 3 |

The remaining results are the functorial layer (Files 4–5):

| Result | Lean name | File |
|---|---|---|
| simplicial map on edges / identities / homotopies | `Edge.map`, `Edge.map_idEdge`, `Homotopic.map` | 4 |
| induced map on hom-classes | `SSet.HoCat.mapHom` | 4 |
| image of a filler is a filler | `Edge.map_compRep_homotopic` | 4 |
| induced functor `hF : hX ⥤ hY` | `SSet.HoCat.map` | 4 |
| **Theorem III**: `X ↦ hX` is functorial | `SSet.HoCat.map_id`, `SSet.HoCat.map_comp` | 4 |
| `homEquiv` commutes with `N F` | `homEquiv_map_nerveMap` | 5 |
| **Theorem IV**: `h(N C) ≌ C` natural in `C` | `nerveHoCatFunctor_natural` | 5 |
| `h(N F)` is an equivalence when `F` is | `nerveHoCat_preserves_equivalence` | 5 |
| stable public wrappers | `homotopic_equivalence`, `comp_well_defined`, `HoCat_category`, `nerve_HoCat_equiv` | API |

---

### How I think about what this is, and what might come next

One way to read the whole thing: an ordinary category can be built from generators and relations (objects, arrows, and equations between composites of arrows). A quasi-category is the homotopical version
of that idea, where "equations between composites" are softened into "fillers witnessing composites".
The homotopy category `hX` is what you get by collapsing those witnesses back down to honest equality.
From that angle, Theorem II (`h(N C) ≌ C`) is the reassurance that the softened world restricts
correctly to the strict one, and Theorems III–IV say the restriction is functorial: `X ↦ hX` is a
functor, and `C ↦ h(N C)` is natural and carries equivalences to equivalences.

*Things to maybe look at next (note to self, not a roadmap).* A couple of directions I'd consider if I
come back to this, listed so I don't forget them, not as commitments, and not claiming they're the
right or only next steps:
- the general statement that a *quasi-categorical equivalence* `X ⟶ Y` induces an equivalence
  `hX ≌ hY` (the version for arbitrary equivalences, beyond images of ordinary functors); I don't yet
  know how hard this is; **check later**;
- some first concrete examples that exercise the now-functorial `X ↦ hX` on more interesting inputs.

Both would build on the structure tagged as `hocat-functorial-core-v0.1`. If either turns out to be the
wrong thing to chase, that's fine. This section is a memory aid, not a plan I'm bound to.
