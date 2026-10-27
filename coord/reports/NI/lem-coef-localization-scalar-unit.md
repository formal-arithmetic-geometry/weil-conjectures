## Worker report

The module `Sheaf.Paper.LocalizationScalarUnit` states
`WeilConjectures.coefficientLocalizationScalarUnit`, with proof `sorry`.
It adds no definitions, axioms, hypotheses of coefficient flatness, or arbitrary comparison maps.
The item's natural-language statement and proof are unchanged.

The previous worker confused Q159's stage-1 PASS with completion of stage 2.
The live item has `reviewed` (the split review), but neither `lean` nor
`reviewed_lean`; Q159's report explicitly says that no Lean statement was supplied.
There is no repair note for this item. This delivery supplies the missing statement.

Hypothesis and clause audit:

- The fixed algebraic closure of a finite field is `D : FiniteFieldDatum`; its field is
  `D.k`. The prime is `l` with `[Fact l.Prime]` and `_hl : l ≠ D.p`.
- The two finite extensions are `E L : Type u`, their field instances, their
  `Algebra (Padic l)` instances, and `FiniteDimensional (Padic l)` instances.
  `m n : ℕ` encode the source's positive exponents as `m+1,n+1`; the existing
  `finiteClosedCoefficient l E m` is literally `Padic.coefficientExtensionRing l E (m+1)`.
  Every positive level is covered, including exponent one. No relationship between
  the two extensions or between their exponents is imposed.
- The arbitrary unital ring map is the binder `φ : ULift A →+* ULift B`.
  These are the same rings with the canonical universe lift; lifting and lowering
  ring homomorphisms are inverse. No `Algebra A B`, flatness, or finite projective
  dimension is assumed. Finiteness of B follows from its actual coefficient construction.
- `X Z U : Over (Spec (.of D.k))` and the separated, locally-finite-type and
  quasi-compact structure-map instances express exactly the separated finite-type
  k-scheme setting. `i : Z ⟶ X` and `j : U ⟶ X` are morphisms in that over category,
  so both are k-maps. `IsClosedImmersion i.left`, `IsOpenImmersion j.left` and `_hij`
  express the specified complementary closed/open pair. U is any presentation of the
  open complement, rather than a restriction to one chosen model of that open subscheme.
- The derived objects live in the existing `finiteClosedDerived`, namely
  `DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u+1} (ULift A)))`.
  This is the actual small pro-etale site with object universe u+1 and hom universe u.
  It is the canonical fixed-coefficient presentation of constant module sheaves.
- `finiteClosedScalar φ T` is the existing ordinary, uncompleted derived extension,
  `ProEtale.pbcFixedScalarExtension`, with its exact derived restriction adjunction.
  `finiteClosedPush` is the ordinary total right-derived `lowerStar`, and
  `finiteClosedPull` is the published left-derived inverse image (exact inverse image
  with its canonical derived identification). These are not completed scalar operations.
- The binder `M` and `_hM : finiteTorConstructibleProEtaleModule ... M` express
  precisely M in the recorded intrinsic bounded constructible finite-Tor category.
  `_hMB` is the same predicate on S_X M with L coefficients.
- N_A and N_B are not independently supplied objects: every occurrence is the actual
  `finiteClosedExceptional A i.left` applied to M or its B scalar extension.
  This is `ProEtale.sfFiniteExceptionalFixed` at `Compactification.ofIsProper i.left`,
  i.e. Rnu_* followed by the specified etale exceptional adjoint followed by nu^*.
  `_hNAB` states the finite-Tor constructibility of S_Z N_A, and `_hNB` that of N_B.
- `_hNA` and `_hJM` unpack exactly the two specified etale origins: there exists an
  etale derived object K satisfying `finiteTorConstructibleEtale`, with an isomorphism
  from its actual comparison pullback to N_A or j_A^* M. They impose no chosen
  identification or selected flat model, and make no assumption about arbitrary
  ambient pro-etale exceptional adjoints.
- The first four conclusion factors are `IsNoetherian U.left`, `QuasiCompact j.left`,
  `IsSeparated j.left` and `LocallyOfFiniteType j.left`. The last and the second together
  are the source's finite-type assertion about j.
- The next conclusion is existence of a connecting arrow δ making
  `Triangle.mk (S_X.map ε_A) (S_X.map η_A) δ` distinguished in the actual B derived
  category. Here ε_A is the existing `finiteClosedCounit A i.left M` and η_A is
  `(ProEtale.derivedUpperStarLowerStarAdjunction ... j.left).unit.app M`.
  Thus both displayed arrows, their objects and their order are fixed. The connecting
  arrow is existential, exactly as the source's final unnamed triangle arrow. The proof
  plan computes it by scalar extension of the A connecting arrow with its shift comparison.
- The next conclusion gives the B localization triangle in precisely the same form,
  using ε_B at S_X M and the ordinary B open unit at S_X M. There are no arbitrary
  adjunctions or functor variables in either triangle.
- The next two factors say `IsIso` of the exact named
  `ProEtale.finiteCoefficientChangeDirectImageMap φ i.left N_A` and its j version at
  j_A^* M. These are the recorded lem-coef-finite-direct-image comparisons, uniquely
  fixed by `IsFiniteCoefficientDirectImageMap`, whose equation is extension of the
  A counit transposed under the B geometric adjunction. No unspecified isomorphisms
  replace these arrows.
- The final equation is, in Lean's left-to-right composition order,
  `S_X.map η_A ≫ c_j ≫ Rj_B.map r_j = η_B`. It expands the source's d_j as c_j
  followed by the direct image of r_j. The latter is exactly
  `(finiteClosedScalarPullIso φ j.left).inv.app M`, the inverse of the existing
  conjugate-adjunction tensor/pullback isomorphism, normalized by the sectionwise
  restriction comparison. The result is equality of morphisms in D(B), without
  applying scalar restriction or merely identifying cohomology objects.

Dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the quotient constructions imported
  from `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and its topology. The morphism-properties node is only an index: its own statement
  explicitly fixes no notion. The actual properties are Mathlib's `Over`,
  `IsClosedImmersion`, `IsOpenImmersion`, `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact`, rather than a fabricated structure for that index node.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` reexports
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem from
  `DerivedChangeOfRingsCochainModel`, as well as the ordinary-module presentation.
  Its universal K-flat computation is the ordinary derived scalar construction;
  the item uses the already published equivalent scalar/restriction-adjoint presentation.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`;
  `FiniteTorAmplitudeProEtaleModule`: `finiteTorConstructibleProEtaleModule`, defined
  from the same `finiteTorConstructible` by the canonical intrinsic realization.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` publicly supplies the
  recorded coefficient-system interface. The actual finite functor used here is
  `ProEtale.sfFiniteExceptionalFixed` from `SfFiniteExceptionalInverseImage`, the
  recorded dependency's already-published finite construction. Its relative counit is
  `ProEtale.rightDerivedUpperShriekCounit`, with the canonical identification
  `rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar` for the closed immersion.
- `Sheaf.Paper.SfDerivedDirectImage`: its finite-level ordinary direct image is
  `proEtaleConstantDerivedDirectImage`, canonically in the same presentation as
  the `lowerStar.rightDerivedFunctor` in `finiteClosedPush`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Triangle.mk`,
  `Pretriangulated.distTriang` and `CategoryTheory.Pretriangulated`.
- `Sheaf.Paper.FiniteCoefficientDirectImage`:
  `ProEtale.finiteCoefficientChangeDirectImageMap`,
  `IsFiniteCoefficientDirectImageMap`, and the etale-origin isomorphism theorem.
- `Sheaf.Paper.FiniteClosedShriek` supplies ONLY existing named definitions in the
  signature: `finiteClosedDerived`, `finiteClosedCoefficient`, `finiteClosedScalar`,
  `finiteClosedPush`, `finiteClosedPull`, `finiteClosedExceptional`,
  `finiteClosedCounit`, and `finiteClosedScalarPullIso`. None of that module's
  closed-shriek change-of-coefficients theorems is used. Rewriting these notions in
  this module would create the forbidden second definitions.

Proof imports are `SfLocalizationAllStages`, `RingedTopoiDerivedPullbackIndependent`,
canonical finite-coefficient `UpperLowerStar.ClosedImmersion`,
`SecSmoothPurity.DirectImageScalarOperations`, and Mathlib `Adjunction.Mates`.
They give the exact plan in the node's five steps; the geometry leaves come from
Mathlib Noetherian and finite-type APIs. The legacy non-finite-coefficient
`UpperLowerStar.ClosedImmersion` listed on the exactness node is not imported,
so its duplicate declarations are avoided; the current finite-coefficient module is
already the implementation used by the canonical exceptional functor.

Import-cycle note for the maintainer (stage 2 §3.7): the existing parent module
`Sheaf.Paper.FiniteClosedShriek` owns the reusable definition interface. The later
proof-dependency import of `LocalizationScalarUnit` into that parent module must
therefore be omitted. There is no declaration-level circular proof: the theorem
here only uses the parent's definitions and is independent of every theorem there.
This is the standing rule's explicit exception for proof imports closing an import cycle;
no DAG dependency is added to the parent and no downstream theorem is used.

Edge cases checked before writing: empty U (open terms and units are zero), empty Z
(identity open), empty X, identity coefficient map, exponent one on either side,
and the nonflat quotient Z/ell^2 to Z/ell. The predicate on Tor amplitude is with
respect to each object's own coefficient ring, not Tor dimension of B over A.
The conclusion consists of genuine derived triangles, not per-degree isomorphisms.
No maximum or dimension of an empty scheme is used. No universe equality between
objects and morphisms of the pro-etale site is imposed.

Searches performed with msearch.py:

- leanfinder: "Derived scalar extension of pro etale closed open localization triangle
  preserves ordinary open adjunction unit". Eight hits: generic derived adjunction
  normalization and algebraic ring localization; no whole-statement match.
- loogle: "CategoryTheory.unit_mateEquiv, CategoryTheory.Functor.map_distinguished".
  Zero combined hits. The individual generic mate statement was also read directly.
- grep: "unit_mateEquiv|map_distinguished", restricted to CategoryTheory.
  25 hits, including Mathlib `Adjunction/Mates.lean:136` and triangulated functor
  lemmas. These are proof tools and do not state the full item.
- leansearch: "Derived extension of coefficients transports the exceptional closed
  support triangle and its open adjunction unit on the pro etale site".
  Eight hits, including generic derived units, sheaf-adjunction units and ordinary
  scalar units. None fixes the two finite pro-etale localization triangles and maps.

Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
`coefficientLocalizationScalarUnit`, `localizationScalarUnit`, and
`localization_scalar_unit` found no existing declaration of this item. Broader searches
for scalar/unit and localization located the parent definitions above and the
all-stage localization records. Their scalar-unit compatibility is a predicate on
supplied comparison isomorphisms, not this theorem about the specified nonflat
ordinary coefficient maps. The older parent closed-shriek theorem asserts a different
exceptional coefficient comparison; it does not state this item.

Source read: the assigned master blueprint node
`sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-closed-shriek.md`,
proof paragraphs 1–2, and the assigned node's complete five-step proof. The current
node has no blueprint_update replacing that source. The exact prescribed unit-mate
formula was checked in Mathlib `Adjunction/Mates.lean:136–138`.
No statement correction, new notion, dependency-record repair, or statement dispute
was necessary.

Validation: server compilation via scompile.py; the final delivery preflight and its
per-file server compile are recorded by deliver2.py. Only this sandbox was edited.

## Second reading by NI

No independent worker reading is claimed. This dispatcher-started worker was instructed
not to start other agents; the maintainer's independent review reads the delivery.
The hypothesis-by-hypothesis self-check above is the author's check, not an independent review.
