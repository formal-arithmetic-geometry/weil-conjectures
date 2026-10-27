## Worker report

The item is stated by `DerivedCategory.ExteriorCohomology.perfect_derived_bialgebra_exterior_rigidity`
in `Sheaf.CategoryTheory.DerivedCategory.PerfectDerivedBialgebraExteriorRigidity`.
Its proof is `sorry`; all helper definitions have real data. No existing node statement was changed.

Clause-by-clause rendering:

- The commutative ring is `R : CommRingCat.{u}`; its existing structure supplies `CommRing R`.
  `IsNoetherianRing R` says every ideal is finitely generated, and `IsLocalRing R` gives the
  maximal ideal and `IsLocalRing.ResidueField R`. The scalar map is the actual `algebraMap`
  to this quotient, bundled with `CommRingCat.ofHom`.
- `K : PerfectScalar.D.{u,w} R` is the existing `DerivedCategory (ModuleCat R)`.
  The explicit instance family `∀ A : CommRingCat.{u}, HasDerivedCategory.{w} (ModuleCat A)`
  is the published scalar-coherence API's choice of localization size, not a restriction on R.
  It covers the ordinary standard universe choice and permits arbitrary compatible sizes.
- `hK : IsPerfectRingComplex K` uses exactly the recorded bounded finite-projective predicate.
- `hB : @BimonObj ... K` supplies precisely u, multiplication, counit and comultiplication.
  Its `MonObj` fields assert associativity and both unit laws; `ComonObj` asserts
  coassociativity and both counit laws; its four bimon fields say comultiplication and
  counit preserve products and units. The braiding is explicitly
  `DerivedMonoidal.braidedCategory' Qh (HomotopyCategory.quasiIso ... (.up ℤ))`, so it is
  the signed total tensor symmetry, rather than an arbitrary braided structure.
  `hC : @IsCommMonObj ... K hB.toMonObj` is multiplication's symmetry invariance.
- `PerfectScalar.B` along the residue quotient is the recorded derived scalar extension.
  `scalarUnit` uses `coherenceData.unit.inv` then B(u); `scalarMul` uses
  `coherenceData.tensor.inv` then B(mu), so these are the induced operations.
- `hFinite` states finite-dimensionality of residue H1 as `Module.Finite` over the residue
  field. `hResidue : IsExterior (scalarUnit ...) (scalarMul ...)` states that the induced
  residue product is exterior, generated in degree one. In degree zero the pure empty wedge
  must map to `unitClass`, so the linear equivalence e0 says H0 is k by u. Negative degrees
  vanish as required by the graded exterior algebra, with no truncation of the derived object.
- The conclusion supplies `P : CochainComplex (ModuleCat R) ℤ`, the zero-outside predicate
  with bound exactly `Module.finrank k H1(residue K)`, `P.d i (i+1) = 0`, and
  `Module.Free R (P.X i) ∧ Module.Finite R (P.X i)` for every integer degree.
  All other differentials are automatically zero for the cochain shape.
  `Nonempty (K ≅ Q.obj P)` is the required isomorphism in D(R).
- `IsIso ((homologyFunctor ... 0).map MonObj.one)` is H0(u), whose source is H0 of the
  canonical tensor unit R[0]. It therefore identifies H0(K) with R.
- `Nonempty (H1(K) ≅ ModuleCat.of R (Fin (Module.finrank k H1(residue K)) → R))`
  says H1(K) is free of precisely rank g. This does not merely claim that some free rank exists.
- `∀ x, cup MonObj.mul 1 1 x x = 0` is exactly the degree-one square-zero assertion.
- The final `IsExterior MonObj.one MonObj.mul` gives linear isomorphisms from each exterior
  power to the corresponding cohomology, normalized on every pure wedge by iterated actual
  multiplication, with the empty product the unit. Since these products are associative and
  multilinear, normalization on the pure-wedge spanning sets is exactly multiplicativity of
  the direct sum isomorphism; it is the stated graded R-algebra isomorphism. Negative degrees
  vanish too. No unrelated multiplication or arbitrary linear isomorphism is substituted.

Dependencies read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  Q; cohomology is the canonical `homologyFunctor` from HomologySequence.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex` (bounded finite-projective model, independent w).
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` and `ExteriorPower.Basic`: existing
  `ExteriorAlgebra`, exterior powers, and `exteriorPower.ιMulti`, no second exterior algebra.
- New definition node `def-sfb-derived-exterior-cohomology`: the canonical cup, unit class,
  natural-degree products, normalized exterior condition, and induced scalar operations.
- Its scalar transport uses the existing
  `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence`, in particular B,
  `coherenceData.unit` and `coherenceData.tensor`. These comparisons are determined by their
  finite-projective representative normalization; no arbitrary tensor map is chosen.
- `WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective`:
  `homSingleEquivOfProjective` and `homSingleToHomology` give the UNIQUE morphism from R in
  degree n for a cohomology element. `representative` invokes the inverse equivalence, so
  there is no choice from mere existence. `singleDiagonal` uses the existing single-shift
  comparison, `singleFunctorObjUnitIso`, shifted unit inverse, and `shiftTensorShiftIso`.
  TotalComplexShift's source confirms the first shift has no sign and the second contributes
  (-1)^(first degree times second shift); with both unshifted factors the unit this is 1.
- `Mathlib.CategoryTheory.Monoidal.Bimon_`: BimonObj, and the inherited IsCommMonObj.
  This existing categorical definition supplies all bialgebra equations rather than copies.

The item imports every recorded available proof-dependency module, privately, with the exact
upstream modules preferred for finite-projective localization, pseudo-coherence, minimal models,
bounded-flat K-flatness and residue localization. The full twelve-step DAG argument is reproduced
in the theorem docstring, including its named dependencies and characteristic-two calculation.

Edge cases checked before finalizing: g=0 forces degree-zero support and H1=0; g=1 has H2=0;
a field makes the residue extension the identity up to canonical comparisons; nonreduced and
noncomplete Noetherian local rings are included; characteristic two is retained (no invertibility
of 2); all integer cohomology degrees and n=0 exterior products are included. The zero ring is
not a local ring with a maximal ideal under the node's convention. No extra characteristic,
regularity, completion, flatness of K's cohomology, or cocommutativity hypothesis appears.

Searches made:

- msearch LeanFinder: `perfect complex commutative derived bialgebra exterior algebra residue
  local ring rigidity`, then `perfect derived bialgebra exterior algebra rigidity`: exterior
  algebra universal properties and square-zero lemmas, no rigidity result. Those exterior
  definitions are used directly.
- msearch Loogle: `CategoryTheory.Bimon, DerivedCategory, ExteriorAlgebra` and then
  `CategoryTheory.BimonObj`: the latter gives BimonObj and its existing field projections.
- msearch LeanSearch: `cohomology cup product monoid object derived category modules` and
  `canonical cup product cohomology derived category algebra object`: general MonObj,
  preadditive derived category, homology and Ext hits, no cup on an arbitrary derived algebra.
- msearch grep `Bimon|Bialgebra|MonoidalCategory` in CategoryTheory/Monoidal found the existing
  BimonObj; grep `homSingleEquivOfProjective|ExteriorCohomology|IsExterior` in Mathlib
  Algebra/Homology/DerivedCategory gave 0 hits. Direct rg in WeilConjectures and Sheaf found
  the existing projective-single equivalence and scalar-coherence machinery, but no exterior
  cohomology predicate or this local-ring rigidity statement. Blueprint-node search
  `derived bialgebra` and `exterior cohomology` gave 0 matches. DAG concept searches found
  sheaf-specific cup products; they do not define cup for arbitrary objects of D(R).
- The current blueprint's direct-images statement and proof were read. This item is the
  auxiliary obstruction calculation in the inherited chain, not that blueprint unit's own
  statement, just as the accepted split records. No blueprint statement correction is needed.

## New nodes

`def-sfb-derived-exterior-cohomology` supplies the missing normalized induced-product interface.
It reuses all existing derived, exterior and scalar-extension constructions. Each definition is
explicit: a unique representative is inverted, tensor of representatives is composed with the
actual multiplication, products recurse with the actual unit, and scalar operations use the
recorded normalized comparisons. `IsExterior` packages degreewise exterior-power linear
isomorphisms with their pure-wedge values, including n=0 and negative-degree vanishing. Its source
is the item's agent-stated induced-product/exterior clause, with Stacks 064B for the representative
convention and 06Y6/0GWN for scalar comparison. The three required search types above are recorded
in the node. Ancestor search returned null; the inherited null ancestor and full via chain are
retained without inventing a blueprint ancestor.

## Second reading by Q44

Author's second pass (the dispatcher forbids subagents and the maintainer performs the independent
reading): I reopened the original JSON, all three recorded statement-dependency signatures and
the final two Lean files, and matched every clause in the list above. The initial drafting pass
was repaired before delivery: the exterior assumption belongs on the residue object rather than
K; the support and H1 rank use the actual residue finrank; all instance sizes are explicit;
BimonObj uses the canonical derived braiding; square-zero and exteriority are separate conjuncts,
outside the universal x binder. The helper contains no postponed theorem. H0 unit normalization
is included through the n=0 pure-wedge condition. Inverting projective-single equivalence is a
construction of the unique class representative, not a choice of an unspecified object.
No STATEMENT-DISPUTED issue or statement correction remains.
