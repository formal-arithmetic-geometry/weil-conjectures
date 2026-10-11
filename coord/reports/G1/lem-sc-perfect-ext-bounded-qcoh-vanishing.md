## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectHomGap` states
`AlgebraicGeometry.Scheme.exists_subsingleton_hom_of_isPerfect`, with the sole proof
`sorry`. No definitions or further nodes are needed. The node is unchanged outside `lean`.

Source checked: Stacks `perfect.tex`, label
`lemma-ext-from-perfect-into-bounded-QCoh`, Tag 09M4, Lemma 36.13.5(1).
The repository's literature checkout is absent on this machine; the same source is available
at `/home/ubuntu/c1-stacks-review/perfect.tex`, lines 3247–3310. Part (1) is exactly the
node's statement; part (2) is not part of this node. In particular L need not be bounded.

Hypothesis and clause correspondence:
- A scheme X: `(X : Scheme.{u})`.
- X quasi-compact: `[CompactSpace X]` (compactness without any Hausdorff assumption).
- X quasi-separated: `[QuasiSeparatedSpace X]`.
- K an object of D(O_X): `(K : schemeDerivedCategory X)`.
- K perfect: `(hK : IsPerfect X K)`, using the recorded local strictly-perfect definition.
- Integers a and b, depending only on X and K: `∃ a b : ℤ`, before quantifying over L.
- Ordered, closed interval: `a ≤ b` and the two implications `a ≤ i → i ≤ b →`.
- Every L in D_QCoh(O_X): `∀ L : schemeDerivedCategory X,
  schemeDerivedQCohProperty X L →`. This is the underlying object with precisely the
  property defining the recorded full subcategory, and adds no boundedness assumption.
- H^i(L) zero at every integer in that interval: `∀ i : ℤ, a ≤ i → i ≤ b →
  IsZero ((DerivedCategory.homologyFunctor
  (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj L)`.
  This is categorical vanishing of the O_X-module cohomology sheaf, not of global cohomology.
- Hom(K,L) zero: `Subsingleton (K ⟶ L)`. The derived category is preadditive, so its Hom
  type has a zero morphism, and being a subsingleton says exactly that every morphism is zero.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; read the locally affine
  locally ringed space structure and its Hom signature/docstring in the pinned Mathlib.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`
  and `AlgebraicGeometry.schemeDerivedQCohProperty`; their full signatures/docstrings
  were read in `lean/Sheaf/AlgebraicGeometry/DerivedCategory.lean`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`;
  its full signature/docstring and the underlying `IsStrictlyPerfect` were read.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, read with its category, abelian and derived-category
  binders; this computes H^i of a cochain complex in the derived category.
The file imports PerfectComplex, which imports DerivedCategory, and
`Mathlib.Topology.QuasiSeparated` for the quasi-separated hypothesis.

The explicit `HasDerivedCategory.{w}` binders for X and all opens are the localization
structures required by the recorded IsPerfect definition; they assert no extra geometric
hypothesis. All universes and variables are explicitly bound, with the module-sheaf carrier
and canonical abelian instance used by the dependency, rather than a second X.Modules
category instance. No field, Noetherian, separated or nonempty hypothesis is added.

Edge cases checked before drafting: the empty scheme is allowed (perfectness is vacuous
there, and its derived category has only zero morphisms); the zero perfect object and the
zero target cause no issue; a=b permits a singleton gap; negative endpoints are retained
by using ℤ; endpoints are inclusive. Targets may have cohomology outside both ends,
even in infinitely many degrees. Neither X nor K nor L is required nonzero or bounded,
and no restriction on characteristic occurs. The Hom type is never subjected to IsZero.
The complete four-step natural-language proof from the node is included in the docstring,
including the qcqs cohomological bound and the truncation argument. No node faults found.

Searches for existing declarations (real tool calls, logged in searches.jsonl):
- msearch.py leansearch: "Maps from a perfect complex on a quasi-compact quasi-separated
  scheme vanish if the target has a gap of quasi-coherent cohomology"; service unavailable
  (Internal Server Error), recorded without a mathematical verdict.
- msearch.py leanfinder: "Hom from a perfect complex vanishes into a complex with
  quasi-coherent cohomology vanishing in a bounded interval"; eight generic derived-category
  hits, including injective/projective single-complex vanishing and t-structure facts.
  None is the scheme-level statement for locally perfect K and quasi-coherent L.
- msearch.py loogle: `DerivedCategory.homologyFunctor, Subsingleton`; zero hits.
- msearch.py grep of Mathlib: `perfect.*vanish|vanish.*perfect|ext.*bounded.*QCoh`;
  zero hits.
- rg on WeilConjectures and lean/Sheaf:
  `perfect.*vanish|vanish.*perfect|perfect-ext-bounded-qcoh-vanishing`; upstream hits are
  unrelated Poincare-duality/Weil-complex finiteness or direct-image assertions; no match
  in lean/Sheaf. Literal item grep in WeilConjectures has zero hits.
- rg on dag/lean_names_upstream.json and both source trees for the selected declaration
  name `exists_subsingleton_hom_of_isPerfect`: no collision. The upstream name table's
  other perfect/gap/exists-subsingleton hits concern ample-module Serre vanishing.

Validation: server single-file compilation and `deliver2.py --no-push` are run below;
the independent second reader will supply their own section and deliver the item.

## Second reading by G1

The node introduces a scheme `X`, with quasi-compact and quasi-separated instances;
the Lean binders are `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`.
It introduces a perfect derived object `K`; Lean uses the shared
`schemeDerivedCategory X` carrier and `hK : IsPerfect X K`, with exactly the
`HasDerivedCategory` instances required by those dependency declarations.  The
statement introduces integers `a,b` with `a ≤ b`; Lean writes `∃ a b : ℤ, a ≤ b`.
For every `L : schemeDerivedCategory X` satisfying
`schemeDerivedQCohProperty X L`, the gap clause is rendered as
`∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor
(SheafOfModules (moduleRings X.toRingedSpace)) i).obj L)`.  The conclusion is
`Subsingleton (K ⟶ L)`, exactly expressing that every morphism is zero in the
preadditive derived category.  Quantifier order and interval inclusivity match
the node exactly.

Edge cases were checked: `a = b`, negative endpoints, zero `K` or `L`, an empty
scheme, and targets with cohomology outside the finite interval are all allowed;
there is no characteristic, Noetherian, boundedness, nonzero, or nonempty
hypothesis.  The integer index and both derived-category universes are explicit.

Independent searches: LeanSearch for "perfect complex maps vanish when
quasi-coherent target cohomology has a finite gap" was unavailable (Internal
Server Error; no mathematical verdict). LeanFinder for "perfect complex Hom
vanishing cohomology gap on a qcqs scheme" gave eight generic results, including
single projective/injective complexes and t-structure bounds; none states this
scheme-level theorem. Loogle `DerivedCategory.homologyFunctor, Subsingleton`
returned zero hits. `rg -i 'perfect.{0,60}(gap|vanish|ext)|
exists_subsingleton_hom_of_isPerfect'` on Mathlib, WeilConjectures and lean/Sheaf
found only unrelated perfect-field and coefficient-complex material. The source's
`CategoryTheory/DerivedCategory/Perfect.lean` concerns finite-projective module
complexes, not locally perfect sheaf complexes. No existing exact declaration was
found. I opened all three statement dependency nodes, and the declarations in
DerivedCategory and PerfectComplex: their shared module-sheaf carrier, homology
functor, quasi-coherence predicate, and local restriction definition match the
node. There are no new nodes or dependency modules in this delivery, no hollow
definitions, no extra proved results, and no statement correction to audit.
The worker module already matched the node and its source (Stacks Tag
09M4, Lemma 36.13.5(1)); no mismatch or repair was needed.  Compilation with
`scompile.py` succeeds with only the intended `sorry` proof.
