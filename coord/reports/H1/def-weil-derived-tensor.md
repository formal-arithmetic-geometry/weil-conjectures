## Worker report

The module defines `AlgebraicGeometry.Scheme.derivedTensor`, taking a scheme `Y`, a
commutative ring `A`, complexes `K₁`, `K₂`, and a chosen resolution complex `P` with a
quasi-isomorphism `f : P ⟶ K₁`; it returns the image of `P` in the derived category
`proEtaleDerivedCategory Y A`. The arguments render the node's scheme, coefficient ring,
complexes, chosen resolution, and quasi-isomorphism clauses. The implementation uses
`DerivedCategory.Q` and `HasDerivedCategory.standard`.

Dependency declarations used: `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`
(`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`), `CochainComplex.IsKFlat` and
`CochainComplex.IsKFlatResolution` (`Sheaf.Algebra.Homology.KFlat`),
`CochainComplex.exists_isKFlatResolution` (`Sheaf.Algebra.Homology.KFlatResolution`).
The tensor and restriction notions are recorded by the dependency nodes' Mathlib matches
`HomologicalComplex.mapBifunctor` and `SheafOfModules.restrictScalars`.

Edge cases checked: arbitrary universe `u`, zero complexes, and empty/zero terms are
admitted by the unrestricted `CochainComplex` binders. Searches recorded in the node
include LeanSearch, LeanFinder, and Mathlib grep searches for derived tensor and K-flat
notions; they found no exact existing declaration.

The source statement asks for the total tensor representative; the current Mathlib
pro-etale derived-category abbreviation and K-flat module use incompatible universe and
ring-sheaf presentations. The compiling declaration therefore records the chosen
resolution's derived-category image while retaining all data binders. `STATEMENT-DISPUTED:`
this implementation does not compute the total tensor complex because that presentation is
not typeable against the existing pro-etale abbreviation.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. Every node object is introduced by a corresponding
Lean binder (`Y`, `A`, `K₁`, `_K₂`, `P`, `f`, `_hf`), and the result is the declared
pro-etale derived category. The implementation's known discrepancy with the tensor clause
is documented above.

## Second reading by H1

Read the item node, all five statement dependencies and their recorded declarations,
the blueprint source (read on the server at its recorded path), and Stacks
`sites-cohomology.tex`, Section Flat resolutions, Definition 06YN, Lemma 06YS,
and Definition 06YU. The source assumes a ringed site; it does not impose boundedness,
Noetherianity, a field, a characteristic, or finiteness. The following independent
object/hypothesis/clause inventory supersedes the discrepancies and disputed implementation
in the historical Worker report above. The node's statement itself is correct and unchanged.

1. Scheme Y: section binder `Y : Scheme.{w}`; the site is `ProEt.topology Y`,
   inherited from `def-weil-pbc-proetale-site`. Exact, including the empty scheme.
2. Commutative coefficient ring A: section binders `A : Type w` and `[CommRing A]`.
   `𝓡` is `constantSheaf ... CommRingCat` applied to `ULift A`, and `𝓢` forgets
   commutativity by `sheafCompose ... (forget₂ CommRingCat RingCat)`. Exact:
   the constant presheaf is sheafified, rather than assumed to be a sheaf.
3. Category of A_Y-modules and its unbounded derived category: the complex terms
   are `SheafOfModules.{w + 1} 𝓢`, and the result is the recorded
   `AlgebraicGeometry.Scheme.proEtaleDerivedCategory Y A`. Exact after repairing
   this dependency's constant-ring presentation to form the commutative constant
   sheaf first. The result still localizes complexes at quasi-isomorphisms using
   `HasDerivedCategory.standard`; no replacement category is defined privately.
4. K-flatness: `_hP : CochainComplex.IsKFlat.{w + 1, w} (R := 𝓡) P`.
   Opening the dependency shows precisely `∀ F, F.Acyclic → Tot(F ⊗ P).Acyclic`.
   The resolution predicate there is `QuasiIso f ∧ P.IsKFlat`. Exact; K-flatness
   was entirely absent in the first worker's binder list and is now required.
5. K₁ and K₂: unrestricted `CochainComplex ... ℤ` binders, together with the chosen
   resolution P. Exact; K₂ is now used in the value rather than an ignored binder.
6. Chosen quasi-isomorphism P → K₁: `_f : P ⟶ K₁`, `_hf : QuasiIso _f`, with
   the K-flatness hypothesis in item 4. Exact. No extra degreewise flatness or
   epimorphism hypothesis is added. `exists_isKFlatResolution` was opened: it
   supplies such a choice and more (flat terms and a degreewise epimorphism), but
   this chosen-resolution definition needs no application of its existence proof.
7. Tensor representative P ⊗_A K₂: `CochainComplex.mapBifunctor P K₂ (curriedTensor _)`
   using `SheafOfModules.monoidalCategory 𝓡`. Exact: the recorded tensor-complex
   Mathlib leaf is `HomologicalComplex.mapBifunctor`; its cochain specialization
   in `BifunctorShift` uses direct-sum totalization and signs `1` and `(-1)^p`.
   The source monoidal declaration was opened: it sheafifies the sectionwise
   module tensor, exactly the sheaf tensor from the dependency node.
8. Regard this tensor as an object of D(Y_proet,A): `DerivedCategory.Q.obj` of
   the total tensor complex. Exact. The former `Q.obj P` missed the entire tensor
   clause and is replaced. Dependence on a chosen resolution is intentional:
   independence is a separate DAG lemma, not claimed here.
9. Ring map A → B: `derivedTensorRing` introduces `B : Type w`, `[CommRing B]`,
   and `φ : A →+* B`. Its induced sheaf morphism `α` is `constantSheaf.map` of
   `CommRingCat.ofHom (RingHom.ulift φ)`, then `sheafCompose.map` forgetting to rings.
   Exact; neither injectivity nor flatness of the ring map is assumed.
10. Constant B_Y as an A_Y-module, then derived tensor: `SheafOfModules.unit SB`
    is B_Y as a module over itself; `SheafOfModules.restrictScalars α` makes it an
    A_Y-module. `HomologicalComplex.single ... (ComplexShape.up ℤ) 0` places it
    in degree zero, and `derivedTensor` applies the same chosen resolution.
    Exact. This whole last-sentence clause was missing and is now implemented.

Edge cases: all complexes are unbounded and indexed by all integers, so the zero complex,
zero terms, and degree zero are included. Zero rings and every characteristic are admitted
by `CommRing`; φ can be any unital ring homomorphism. No covers or indexing sets are
required to be nonempty. The empty scheme is admitted by the scheme binder and the topology.
The coproduct over p+q=n is the standard infinite direct sum, not a finite truncation.
Universes are explicitly declared and section variables explicitly bound; `ULift` moves
coefficients into the site's larger universe. The site's object universe is w+1 and its
hom universe w; the revised K-flat dependency takes independent object and hom universes
and uses their maximum for coefficient/module universes. When those universes coincide,
it reduces to the former signature; thus existing equal-universe consumers retain the
same predicate. Arbitrary size data can be accommodated by choosing a common ambient
universe, as in the pro-etale dependency's size convention.

Independent searches (2026-10-11): `msearch.py` LeanSearch query "Tensor product of
unbounded complexes of sheaves using a flat resolution" was unavailable (HTTP internal
server error), so no no-match verdict is inferred from it. LeanFinder query
"Localization of total tensor of complexes on a ringed site at quasi isomorphisms"
returned `Tor`, `Tor'`, and `HomologicalComplex.HasGoodTensor₁₂`: these concern objectwise
projective-derived functors or underived tensors, not this chosen K-flat sheaf model.
The Mathlib grep query `derivedTensor|tensorDerived|leftDerivedTensor|derived.*tensor`
in Algebra/Homology had zero hits. Additional direct rg searches in the entire project's
`lean/Sheaf` and upstream `WeilConjectures` found upstream
`AlgebraicGeometry.ProEtale.derivedTensor` (opened in SixFunctors/ProEtale/Derived/Tensor):
it is on sheaves valued in an abstract coefficient category with extra monoidal closed
and functorial-flat-resolution instances. It is not the node's A_Y-module category or
chosen-resolution definition. `CochainComplex.KFlat` is likewise a subcategory defined
by preservation of quasi-isomorphisms, not the dependency's acyclic-tensor predicate.
No exact existing declaration replaces this delivery. Loogle `"constantCommuteCompose"`
found the standard isomorphism, but its required preservation-of-sheafification instance
is unavailable for this forgetful functor in the compiling library; this motivated the
commutative-first dependency presentation, not an extra hypothesis on the item.
The names of the item declarations and the new supporting monoidality statement were
also checked against Mathlib, the upstream source and the DAG declaration records.

Mismatches repaired: wrong representative `Q.obj P`; missing K-flatness; ignored K₂;
missing ring-map specialization; incompatible ring-sheaf presentation in the pro-etale
category; equal object/hom universe restriction in K-flatness; missing standard header.
All definitions contain actual constructed data, not `sorry`. Only the K-flat dependency's
named supporting proof declarations have `sorry`, each with its source and proof outline.
No mathematical theorem is proved in this stage. No new DAG nodes, no statement correction,
and no private replacement of a dependency notion were needed. All delivered signatures
are copied verbatim from their modules into their node records.

## Dependency modules

`def-weil-pbc-proetale-site`: the previous RingCat-only constant sheaf loses access to
commutativity needed by the recorded tensor and K-flat declarations. The delivered
ProEtaleDerivedCategory module forms the same constant A_Y by sheafification in
CommRingCat and then forgets to RingCat; it retains the small pro-etale site, the category
of module sheaves, and the standard localization-derived category. Read against the
node and its blueprint source: all its mathematical objects and assumptions are retained.
Only the node's `lean` record changes; the module uses the same declaration name.

`def-pc-kflat-complex`: the old declaration imposed equal object and morphism universes,
whereas Mathlib's ProEt site has objects in w+1 and morphisms in w. The delivered module
separates those universes, taking their maximum for coefficients and modules. It keeps
exactly the source's acyclic-complex test, total sheaf tensor, and quasi-isomorphism
resolution predicate. Its new supporting named instance
`SheafOfModules.isMonoidal_W_separateHomUniverse` states monoidality of the tensor
localization in these universes, with the source internal-Hom/sheafification proof
outlined in its docstring and proof postponed. The existing zero-preservation support
statements are retained, with the generalized universes. Read against Stacks 06YN and
06YS: no boundedness, flat-term condition or other mathematical hypothesis is introduced
into either definition. Only the node's `lean` record changes; its statement and
Mathlib match are retained.

Validation also found that the old K-flat module wrote its two zero-preservation
proofs as `instance ... := sorry`, which the current preflight correctly treats as
hollow data declarations. Both, and the new monoidality support, are now named
`theorem`s with the `instance` attribute. Their propositions and instance behavior
are retained, while every postponed proof is a theorem as required by H5/H6.
