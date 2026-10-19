## Worker report

The module `Sheaf.Algebra.Homology.AlgebraicNormalizedDualizing` defines
`DerivedCategory.IsAlgebraicDualizing` and
`DerivedCategory.IsNormalizedAlgebraicDualizing`, together with the constant-module
transport and the canonical scalar-action arrow used by these definitions. There
are no new theorems or postponed proofs and no new DAG nodes. The item's statement,
source, and dependencies are unchanged.

The previous worker's BLOCKED diagnosis was incorrect: ledger line 41787 records
Q62's stage-1 split, not a stage-2 delivery. The current node has `reviewed` but
neither `lean` nor `reviewed_lean`, and Q62's report explicitly says that no Lean
was written. This delivery supplies the missing stage-2 definition.

Source checked directly: literature/stacks-project/dualizing.tex, Definition 0A7B
(lines 2557 onward) and Section 0A7M, opening paragraph (lines 2906 onward).

Every hypothesis and clause is rendered as follows:

- A commutative Noetherian ring: `(A : Type u) [CommRing A]
  [IsNoetherianRing A]` in both predicates. The global predicate does not assume
  nonzero, local, regular, or finite-dimensional A.
- The ordinary derived category D(A): `DerivedCategory (RingSiteModules A)`, the
  project's established encoding by module sheaves on `Discrete PUnit` with the
  bottom topology and constant ring sheaf `CochainComplex.onePointRingSheaf A`.
  Evaluation at the unique object gives ordinary A-modules. The existing
  `[HasDerivedCategory.{u} (RingSiteModules A)]` is the library's small-Hom size
  convention; it is independent of Ω, not an assumption about its cohomology.
- Clause (i): an existential cochain complex `I`, `∀ i, Injective (I.X i)`, term
  bounds `∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (I.X i)`, and
  `Nonempty (DerivedCategory.Q.obj I ≅ Ω)`. Thus it is a genuinely bounded
  injective representative, with arbitrary integer bounds.
- Clause (ii): `∀ j : ℤ, Module.Finite A` of the value at the unique object of
  `(homologyFunctor (RingSiteModules A) j).obj Ω`.
- Clause (iii): `IsIso (algebraicDualizingScalarAction A Ω)`. This arrow is
  `(SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf A) Ω).homEquiv
  _ _ (λ_ Ω).hom`. The existing adjunction is uniquely normalized by ordinary
  evaluation on K-flat/K-injective representatives, so this is scalar action,
  not an arbitrary arrow into RHom. Its source tensor unit is A[0], under the
  existing derived monoidal construction.
- Locality: `[IsLocalRing A]` appears only in the normalized predicate; its
  maximal ideal and residue field are the canonical Mathlib ones.
- The residue module κ=A/m: `ModuleCat.of A (IsLocalRing.ResidueField A)` uses
  the canonical residue action. `algebraicDualizingModuleSheaf` transports it
  by the constant presheaf with identity restrictions; the bottom-topology sheaf
  proof is the existing `Presheaf.isSheaf_bot`. This helper contains real data.
- M[0]: `(DerivedCategory.singleFunctor (RingSiteModules A) 0).obj` of that
  module sheaf. Both occurrences of κ[0] use exactly this same object.
- Normalization: conjunction with `IsAlgebraicDualizing A Ω` and
  `Nonempty (RHom(κ[0], Ω) ≅ κ[0])`, with RHom the existing `SignedRingedHom.hom`.
  The latter unfolds to `derivedInternalHomOfUniverses`, the recorded dependency.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (Noetherian ring).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; its HomologySequence module supplies
  `DerivedCategory.homologyFunctor` and the singleFunctor supplied by its imports.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`. The complete generic signature
  and construction were read; `SignedRingedHom.homFunctor` specializes precisely
  this declaration to the small ringed site, and `SignedRingedHom.hom` fixes the
  first argument. The evaluation-normalized adjunction is supplied by
  `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`, whose full signatures
  and normalization specification were read.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
  The recorded `InjectiveResolution` signature and docstring were also read;
  the definition needs degreewise injectivity, not a resolution of a degree-zero
  object.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- Existing site helpers: `CategoryTheory.RingSiteModules` in
  `Sheaf.Algebra.Homology.RingHomExtensionDefs`, and
  `CochainComplex.onePointRingSheaf` in
  `Sheaf.Algebra.Homology.KFlatTensorQuasiIso` (publicly imported by the former).

Searches before writing:

- msearch.py leanfinder: "An algebraic dualizing complex over a Noetherian local
  ring with finite cohomology bounded injective representative and normalized
  derived Hom from residue field". Eight hits on cotangent spaces, injective
  dimension, Ext and injective resolutions; no definition of this notion.
- msearch.py loogle: "DerivedCategory, ModuleCat, dualizing". Zero hits;
  dualizing is unknown.
- msearch.py grep: "IsDualizing|NormalizedDualizing|homothety|scalarActionMap".
  Twenty-five unrelated geometric homothety hits; no match.
- rg in the upstream WeilConjectures and side lean/Sheaf sources for normalized
  dualizing, algebraic dualizing and IsDualizing: the existing dualizing objects
  concern etale/six-functor constructions, not this algebraic predicate. The
  semidualizing and complete-local-duality modules inline some of the conditions
  but do not define this predicate. They demonstrate the existing one-object-site
  encoding and canonical scalar-action transpose used here.
- rg in upstream, lean/Sheaf and dag/lean_names_upstream.json for all four proposed
  names and for constantModuleSheaf/onePointModule found no collision with these
  names. The etale constantModuleSheaf in PurEtaleClosedConstantTensor is on a
  scheme's etale site, not the one-object bottom-topology transport here.
- rg of the item id in upstream sources found no existing matching declaration.

Edge cases checked against the source:

- A=0 remains allowed globally; Ω=0 has the required zero representative, finite
  cohomology and scalar-action isomorphism. The normalized predicate uses Mathlib
  locality, which excludes the zero ring, as does the source's local setup.
- Over a field, A[0] is normalized, while a nonzero shift A[t], t≠0, is dualizing
  but fails normalization. The displayed κ[0] has the fixed integer degree zero.
- For nonlocal rings only the global predicate applies. No residue field is
  requested globally.
- General Artinian local rings are covered without regularity or a free-injective
  hypothesis; bounds may be negative and zero terms are allowed.
- The injective representative is existential only inside a Prop: no unknown
  object is defined by choice from a sorry existence proof.

There is no statement correction or statement dispute. All declarations have
source/blueprint docstrings and all variables and universes are explicitly bound.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
