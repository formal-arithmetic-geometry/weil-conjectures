## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineFamilyFppfAlgebra` states
`AlgebraicGeometry.finiteAffineFamily_fppfAlgebra`, with its whole proof `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`. The source read was
`literature/stacks-project/descent.tex`, lemma-flat-finitely-presented-permanence
(Tag 02KL), especially its finite disjoint affine replacement and affine reduction.
The theorem docstring records all seven steps of the node's proof.

Hypotheses and objects:

- Commutative rings R and A: `(R A : CommRingCat.{u})`; base homomorphism:
  `(α : R →+* A)`. Bundling adds no condition such as nontriviality.
- A finite set of indices: `(I : Type u) [Finite I]`. There is no Nonempty or
  Fintype assumption. The explicit common universe is the scheme coproduct's
  size convention; arbitrary finite sets and rings can be represented there.
- The rings and component ring maps: `(B : I → CommRingCat.{u})` and
  `(β : ∀ i : I, A →+* B i)`.
- Component flatness: `hflat : ∀ i : I, (β i).Flat`.
- Component finite presentation: `hfp : ∀ i : I, (β i).FinitePresentation`.
  RingHom.FinitePresentation is exactly Algebra.FinitePresentation for the
  algebra structure induced by that ring map, as the dependency's match records.
- Finite type of each composite: `hft : ∀ i : I, ((β i).comp α).FiniteType`.
- Joint surjectivity on scheme points: `hcover` quantifies every `y : Spec A`
  and supplies `i : I`, `x : Spec (B i)` mapping to y under `Spec.map` of β i.

Conclusions, in the order of the conjunction:

1. `IsIso (sigmaSpec B)` identifies the actual Mathlib scheme coproduct
   `∐ (fun i ↦ Spec (B i))` with `Spec (.of (∀ i, B i))`. The canonical
   isomorphism is `asIso (sigmaSpec B)`, whose hom is precisely sigmaSpec B.
2. `∀ i, Sigma.ι ... i ≫ sigmaSpec B = Spec.map (... Pi.evalRingHom ... i)`
   identifies every coprojection with the spectrum of its product projection.
3. The component-induced maps are the actual `Sigma.desc` families of Spec β i
   and Spec ((β i).comp α). Their first equality is p_Z = q_Z ≫ Spec α,
   i.e. the node's commutative triangle with Lean's left-to-right composition.
4. The next two equalities are q_Z = sigmaSpec B ≫ Spec (RingHom.pi β) and
   p_Z = sigmaSpec B ≫ Spec (RingHom.pi (fun i ↦ (β i).comp α)). Thus neither
   map nor the comparison isomorphism is arbitrary or existentially chosen.
5. `RingHom.pi (fun i ↦ (β i).comp α) = (RingHom.pi β).comp α` states the
   coordinatewise compatibility of the R and A product homomorphisms explicitly.
6. `Flat`, `Surjective`, and `LocallyOfFinitePresentation` apply to exactly q_Z,
   the above `Sigma.desc` family of the spectra of β i.
7. `LocallyOfFiniteType` applies to exactly p_Z, the `Sigma.desc` of the
   spectra of the composite ring maps.
8. `(RingHom.pi β).FaithfullyFlat` and `(RingHom.pi β).FinitePresentation`
   give faithful flatness and finite presentation of A → product B_i.
9. `(RingHom.pi (fun i ↦ (β i).comp α)).FiniteType` is finite type of the
   composite R → product B_i, with its equality to the composite in clause 5.
10. `IsEmpty I → Subsingleton A ∧ Subsingleton (∀ i : I, B i)` explicitly
    includes the empty-family clause. Subsingleton of a commutative ring says
    it is the zero ring (all elements coincide); it does not choose a carrier.

Dependency declarations used, read with their full signatures and docstrings:

- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat,
  `RingHom.Flat` (Module.Flat for the induced algebra).
- def-weil-pbc-finitely-presented-algebra: Mathlib.RingTheory.FinitePresentation,
  `Algebra.FinitePresentation`, through its exact ring-map form
  `RingHom.FinitePresentation` in the same file, explicitly listed in the match.
- def-weil-pbc-finite-type-algebra: Mathlib.RingTheory.FiniteType,
  `RingHom.FiniteType`.
- def-weil-affine-spectrum and def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme`.
- lem-weil-pbc-scheme-coproduct-family has a Mathlib match, requiring no lean
  repair: Mathlib.AlgebraicGeometry.Limits gives the small discrete coproduct
  instance, `sigmaOpenCover`, and `disjoint_opensRange_sigmaι`; its universal
  maps are `CategoryTheory.Limits.Sigma.ι` and `Sigma.desc`, used here directly.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  `AlgebraicGeometry.Flat`.
- def-sbc-locally-finite-presentation:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType` (the statement asks local finite type).
- def-weil-pbc-faithfully-flat-ring-map:
  Mathlib.RingTheory.Flat.FaithfullyFlat.Basic, `Module.FaithfullyFlat`, through
  the recorded exact ring-map notion `RingHom.FaithfullyFlat` in
  Mathlib.RingTheory.RingHom.FaithfullyFlat.

All dependencies resolve to Mathlib. Public imports provide these statement
notions and the canonical coproduct and product constructions. The proof-dependency
matches likewise lie in Mathlib; their affine criteria and faithful-flat criteria
are available through these imports, with no project proof modules to add.

Edge checks before writing and during the second pass: an empty index makes the
product a singleton commutative ring, and the covering condition forces Spec A to
be empty, hence A to be zero. The empty product map R → 0 remains finitely
presented (the quotient by (1)), and all pointwise source properties are vacuous.
Zero factors are permitted and contribute empty components. If A is zero, unital
maps force each factor to be zero, consistently with every conclusion. For a
singleton family the statement reduces to the familiar affine faithfully flat
criterion plus its given finite presentation and finite type. No nontriviality,
nonemptiness, field, characteristic, or additional algebra compatibility is assumed.
No statement dispute or node fault was found.

Searches on 2026-10-24 (the required msearch.py wrapper, group Q101, this item):

- LeanFinder: "A finite jointly surjective family of flat finitely presented affine
  morphisms has a faithfully flat finitely presented product algebra, compatible
  with maps to a base ring". Eight hits, notably
  `AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`,
  `AlgebraicGeometry.flat_and_surjective_SpecMap_iff`, and
  `Algebra.FinitePresentation.pi`; none states the complete two-map package.
- Loogle: `"FaithfullyFlat", "FinitePresentation"`. Two descent results:
  `RingHom.FinitePresentation.codescendsAlong_faithfullyFlat` and
  `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`;
  neither is this statement.
- msearch grep: `sigmaSpec|finiteAffineFamily|faithfullyFlat.*[Pp]i`.
  Eleven hits, including sigmaSpec, ι_sigmaSpec, and the finite IsIso instance
  in Mathlib.AlgebraicGeometry.Limits. These give the canonical comparison
  and its component compatibility but not the assembled theorem.
- LeanSearch: "A finite jointly surjective family of flat finitely presented affine
  morphisms gives a faithfully flat finitely presented product algebra compatible
  with a base ring map". Eight hits, notably Algebra.FinitePresentation.pi,
  RingHom.FaithfullyFlat, and RingHom.FaithfullyFlat.iff_flat_and_comap_surjective;
  these again supply pieces rather than the whole statement.
- Direct rg in both lean/WeilConjectures and lean/Sheaf:
  `sigmaSpec|finiteAffineFamily|lem-a1-finite-affine-family-fppf-algebra`.
  Several unrelated uses of sigmaSpec, but no existing complete statement or
  declaration for this node. The required literal-node search of the upstream
  sources likewise found no matching declaration. A final name search for
  `FiniteAffineFamilyFppfAlgebra|finiteAffineFamily_fppfAlgebra` found no collision.

Validation: scompile.py compiled the one delivered file cleanly in sandbox and
library module modes, about seven seconds each; only the expected sorry is left.
All variables and universe u are explicit. No diagnostic commands remain.

## Second reading by Q101

I performed a separate second pass over the node statement and the completed
Lean file. This is a solo-worker rereading; no separate agent was started, per
the dispatcher's instruction. I checked the component ring maps in hflat/hfp,
the composites in hft and p_Z, the pointwise hcover, the actual product and
coproduct constructions, and every conjunction against the numbered mapping above.
In particular, the isomorphism uses sigmaSpec itself, its coprojection identity
uses the correct product projection, the triangle reads p_Z = q_Z ≫ Spec α,
and both coordinate-map comparisons refer to that same sigmaSpec. The flat,
surjective, and local finite presentation predicates refer to q_Z, whereas local
finite type refers to p_Z. Both product ring properties over A and finite type
over R are present. The empty-family implication states both A = 0 and the
zero-ring empty product using Subsingleton. No mismatches were found, and no
statement change or replacement construction was necessary. The independent
maintainer review remains the separate review described by the dispatcher.
