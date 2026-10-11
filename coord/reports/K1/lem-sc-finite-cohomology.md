## Worker report

The module states `DerivedCategory.finite_homology_of_isMPseudoCoherent`, with its sole
proof `sorry`. It is exactly the first assertion of [Stacks Tag 064S](https://stacks.math.columbia.edu/tag/064S).
No new definition or dependency module is needed: the landed
`DerivedCategory.IsMPseudoCoherent` is reused. No mathematical dispute remains.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The ring is `{R : Type u} [CommRing R]`, explicitly following
  [Stacks Tag 00AQ](https://stacks.math.columbia.edu/tag/00AQ). No `Nontrivial`, Noetherian,
  characteristic, or field assumption is imposed.
- The integer is `(m : ℤ)`, allowing all positive, zero, and negative degrees.
- The complex is `(K : CochainComplex (ModuleCat.{v} R) ℤ)`; its object in D(R) is
  `Q.obj K`. The category is Mathlib's actual localization, not an abstract proxy.
- The pseudo-coherence hypothesis is `hK : IsMPseudoCoherent m (Q.obj K)`.
  On opening its recorded definition: `∃ E a b` with `E.IsStrictlyGE a` and
  `E.IsStrictlyLE b` renders boundedness; `∀ i, Module.Free R (E.X i) ∧
  Module.Finite R (E.X i)` renders finite free terms; `∃ f : Q.obj E ⟶ Q.obj K`
  is the required derived morphism; `∀ i, m < i → IsIso (H_i.map f)` is the
  isomorphism clause above m, and `Epi (H_m.map f)` is surjectivity in degree m
  in the category of modules. Thus every clause of the inline definition is preserved.
- Vanishing above m is `hvan : ∀ i : ℤ, m < i → IsZero
  ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj K))`. It imposes no condition at m.
- The conclusion is `Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj
  (Q.obj K))`, exactly finite generation of H^m, with no finite presentation assertion.
  Mathlib's `homologyFunctorFactors` identifies this module with `K.homology m`.

Dependencies read and used:

- `def-weil-abstract-derived-category` is a Mathlib leaf, recorded by
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, declaration `DerivedCategory`,
  with `HasDerivedCategory` and `DerivedCategory.Q`. Its signatures and docstrings
  were read. `DerivedCategory.homologyFunctor` and `homologyFunctorFactors` are in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` (read in full at their
  declarations); these reach the module through the single used import.
- The newly added dependency, already landed as `def-pc-ring-m-pseudo-coherent`, is
  module `Sheaf.RingTheory.MPseudoCoherent`, declaration `DerivedCategory.IsMPseudoCoherent`.
  Its full file and record were read. It uses independent ring/module/localization
  universes and is exactly Tag 064Q (1).
- `Module.Finite` in `Mathlib.RingTheory.Finiteness.Defs` means that the top submodule
  is finitely generated. `IsZero` is the categorical zero-object predicate.

Edge cases checked before writing: the zero complex, the zero ring, an acyclic complex,
all integers m including m=0 and negative m, and a witness with top degree below m.
All give zero top cohomology when appropriate, which is finite. No nonzero top term
is required in the statement. The proof docstring explicitly covers the all-zero
witness and the below-m case. Rings need not be Noetherian: splitting at the highest
vanishing degree, rather than finite generation of arbitrary kernels, is essential.
Universes `u v w` are explicitly bound and independent, with `HasDerivedCategory.{w}`
recording the chosen localization universe as required by the dependency.

Searches performed (2026-10-11):

- msearch.py leansearch: "m pseudo coherent complex vanishing above m finite type cohomology";
  service unavailable, Internal Server Error, so no search verdict inferred.
- msearch.py leanfinder: "top cohomology of m pseudo coherent complex is finitely generated";
  eight hits on projective/injective resolutions, K-injectivity and degree bounds;
  none states finite top cohomology under this hypothesis.
- msearch.py loogle: "Module.Finite, HomologicalComplex.homology"; zero hits.
- msearch.py grep: "pseudo.?coheren|finite.*homology" in Mathlib/Algebra/Homology;
  eight unrelated exact-functor/Euler-characteristic hits.
- rg over WeilConjectures and lean/Sheaf: "lem-sc-finite-cohomology|[Pp]seudo[Cc]oherent|finite.*cohomology";
  no theorem matching the item. Existing Sheaf files supply `IsMPseudoCoherent` and
  refer to this item in the gluing proof. Source `DerivedCategory.IsPerfect.finite_homology`
  requires a perfect object and a Noetherian ring, so is not the same assertion.
- rg for the exact node id in WeilConjectures: no hits. rg for the proposed declaration
  in dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf: no collision.
- DAG search found `def-pc-ring-m-pseudo-coherent`, already landed, so no duplicate node.

Server validation: scompile.py compiled the module with exit code 0 and no warnings
(1.4 seconds). The report and node record were then prepared for deliver2.py --no-push.

## Statement corrected

Old statement, verbatim:

Let R be a ring and m an integer. Let D(R) be the derived category [def-weil-abstract-derived-category] of the abelian category of R-modules. Call an object C of D(R) m-pseudo-coherent if there are a bounded complex E^\bullet of finite free R-modules and a morphism E^\bullet\to C in D(R) inducing isomorphisms H^i(E^\bullet)\to H^i(C) for i>m and a surjection H^m(E^\bullet)\to H^m(C). If K^\bullet is a complex of R-modules, viewed as an object of D(R), which is m-pseudo-coherent and satisfies H^i(K^\bullet)=0 for every i>m, then H^m(K^\bullet) is a finite type R-module.

The source's ring convention was implicit. Make commutativity with identity, including
the zero ring, explicit, and cite the landed definition of m-pseudo-coherence instead
of leaving its dependency unrecorded. This records the source convention; it does not
restrict the source's class of rings. Sources: [Tag 064S (1)](https://stacks.math.columbia.edu/tag/064S),
[Tag 064Q](https://stacks.math.columbia.edu/tag/064Q), and
[Tag 00AQ](https://stacks.math.columbia.edu/tag/00AQ).
Only `statement`, `stmt_deps`, `statement_change`, and `lean` change. The proof and
proof dependencies are unchanged. The item is a proof-support node, not the unit's
own statement (`blueprint.is = null`). All citers, found by the exact id search and
filtered for statement/proof dependencies, were read:

- `lem-pc-ring-pseudo-coherent-iff-all-m`: holds true. The descending construction applies the lemma over the commutative ring of Stacks Tag 064U, at m=n-1 to its cone; the use still holds.
- `lem-pc-ring-pseudo-coherent-localization-glue`: holds true. The lemma is applied over commutative localization rings A_{f_i} at the top degree n; the use still holds.
- `lem-sc-affine-pseudo-coherent-lift`: holds true. The lemma is applied to complexes over localized coordinate rings of affine schemes, which are commutative with identity; the use at m=n-1 still holds.

## Second reading by K1

I independently opened the corrected node and the Lean module. The node introduces a
commutative ring with identity `R` (including the zero ring), an integer `m`, the derived
category `D(R)`, an object `C` that is `m`-pseudo-coherent, and a cochain complex `K`.
The Lean renders these as `{R : Type u} [CommRing R]`, `(m : ℤ)`,
`[HasDerivedCategory.{w} (ModuleCat.{v} R)]`, `hK : IsMPseudoCoherent m (Q.obj K)`,
and `K : CochainComplex (ModuleCat.{v} R) ℤ`. The dependency declaration
`DerivedCategory.IsMPseudoCoherent` supplies exactly the bounded finite-free witness,
cohomology isomorphisms for every `i > m`, and the degree-`m` epimorphism required by
the node. The node's vanishing clause is rendered verbatim as
`hvan : ∀ i : ℤ, m < i → IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj K))`;
there is no condition at `m`. Its conclusion is rendered as
`Module.Finite R ((homologyFunctor (ModuleCat.{v} R) m).obj (Q.obj K))`, matching finite
type of `H^m(K)` without adding finite presentation or any stronger claim.

The universes `u`, `v`, and `w` are independently bound, and no Noetherian, field,
nontriviality, characteristic, or positivity assumption is present. I checked the zero
ring, zero and acyclic complexes, an empty/vanishing witness, `m = 0`, negative `m`, and
a witness whose top degree is below `m`; the statement admits all of these cases.
The source is Tag 064S (1), and the proof docstring records its three steps: choose the
witness, cancel finite-projective contractible top summands, then descend finite type
along the degree-`m` quotient. Searches in Mathlib, `WeilConjectures`, and `lean/Sheaf`
found no duplicate theorem; the existing `DerivedCategory.IsMPseudoCoherent` dependency
is used directly. I found no mismatch and made no further changes in this reading.
