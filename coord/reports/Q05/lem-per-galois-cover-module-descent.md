## Worker report

The module `Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent` states
`AlgebraicGeometry.GaloisModuleDescent.exists_galoisCoverModuleDescent` with one
`sorry`, and gives real definitions of its site, restriction, representation,
and mixed-tensor expressions. No proof is supplied and no node statement is changed.
The retained earlier attempt contained the main Lean module and search log, but no
node record or report; the initial required dry run reported that missing node file.

The statement is matched clause by clause as follows.

- A scheme S and its nonempty connectedness are `{S : Scheme.{u}} [ConnectedSpace S]`.
  A connected finite etale Galois cover is `(c : S.FiniteEtale)
  [PreGaloisCategory.IsGalois c]`; the finite group is the actual `Aut c`.
  The recorded Galois-object definition is specialized using upstream
  `Scheme.FiniteEtale.galoisCategory` and `isGalois_iff`, rather than replaced by
  an arbitrary finite group or an arbitrary action on the cover.
- The small etale site is its equivalent `SmallModel.{u+1,u,u+1} S.Etale`, with
  topology induced from `S.smallEtaleTopology` along the canonical equivalence.
  This implements the small-representative size convention of proof step 1.
  Coefficients and module carriers are in universe u+1, with no set-finiteness bound.
- Any commutative ring R is `(R : CommRingCat.{u+1})`. An R-module with R-linear
  G-action is exactly `Rep.{u+1} R (Aut c)`, including its equivariant linear maps.
- `Modules S R` is the existing `ringedSiteModules` over
  `constantCoefficientRing (topology S) R`.
  `Trivialized c R` requires an M and an isomorphism between `F.over (coverObject c)`
  and the restriction of the constant M. This is precisely constancy of inverse
  image along the etale cover, computed by slice restriction as in proof step 6.
  A constant sheaf on the slice is canonically the restriction of the constant
  sheaf on the base; M is not required finite. The equivalence ends in exactly
  this property's `FullSubcategory`, and `realization` composes with its inclusion.
- The existential family `E : ∀ R, Rep R (Aut c) ≌ ...` is the descent equivalence
  T for every coefficient ring. Its first conjunct is `.Additive` for realization.
- Its second conjunct is a natural isomorphism from `Rep.trivialFunctor ⋙
  realization` to `constantCoefficientModule`, so trivial representations become
  the constant sheaves, naturally in their modules and maps.
- The third conjunct quantifies over every `ShortComplex` of representations:
  `K.ShortExact ↔ (K.map (realization ...)).ShortExact`. The right side is computed
  in ambient module sheaves, not an assumed abelian structure on the full subcategory.
  Short exactness in Rep is underlying-module short exactness, since kernels and
  cokernels have their induced actions. Via the equivalence this also covers every
  sequence in the full subcategory, in both directions.
- The fourth conjunct is `Module.Finite R V ↔ IsLocallyConstantFiniteTypeModules
  (topology S) R ((realization ...).obj V)`. It uses the recorded sieve-local
  finite-type definition, and includes the converse without a finite-ring assumption.
- The fifth conjunct specifies the descent realization: a natural isomorphism from
  the constant underlying module restricted to Y to the realized sheaf restricted
  to Y, with actual deck-map restriction acting on constant values by `V.ρ g⁻¹`.
  This is the canonical G-descent normalization, not a new hypothesis on V. Sections
  are contravariant, hence the inverse. It prevents an unrelated abstract equivalence
  from standing for descent of the specified action.
- The last conjunct quantifies over every ring morphism `φ : R ⟶ A`, every A-module
  N, and every R-representation V. `mixedRepresentation` uses trivial action on N,
  scalar extension on V, and Rep's tensor, giving action `n ⊗ (a ⊗ v) ↦
  n ⊗ (a ⊗ gv)`. Its actual A-module is `N ⊗_A (A ⊗_R V)`, canonically and
  A-linearly identified with `N ⊗_R V` by balanced tensor associativity. On the sheaf
  side `mixedSheaf` is `N_S ⊗_{A_S} (A_S ⊗_{R_S} T(V))`, the same canonical
  association of `N_S ⊗_{R_S} T(V)`. These are genuine extension-of-scalars and
  sheafified tensor constructions from the recorded tensor dependency.
  `i N V` is an isomorphism in `Modules S A`, hence A_S-linear. Its displayed
  equality is the naturality square for each A-linear f and equivariant R-linear h.
  No flatness, finite generation, nonzero-ring, or finite-underlying-set assumption
  is imposed on these variables.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, which includes `Nonempty`.
- `Mathlib.CategoryTheory.Galois.GaloisObjects`: `PreGaloisCategory.IsGalois`.
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic` supplies its specialization
  and `isGalois_iff` for the finite etale category.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` and `Scheme.Etale`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  exact abbreviation of Mathlib's `SheafOfModules`, with its existing abelian structure.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar` and
  `upperStarLowerStarAdjunction`; the etale specialization is computed using the
  `upperStarIsoLocalizationRestriction` interface from
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` and
  `Scheme.Etale.overEquiv` from `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`.
  Slice restriction itself is the existing `SheafOfModules.overFunctor`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules`:
  `SheafOfModules.IsLocallyConstantFiniteTypeModules`, whose complete definition uses
  covering sieves, finitely generated modules, and isomorphisms on localized sites.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; `Rep`'s monoidal
  structure uses this tensor and the diagonal action. Scalar extension uses the
  existing `ModuleCat.extendScalars` lifted through `mapAction` and the Rep/Action
  equivalence, with no new representation category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor interface; its public imports supply `siteSheafTensorRight`,
  `siteSheafTensorSecondMap`, `changeOfRingsOfUniverses`, and
  `changeOfRingsHomOfUniverses`. Their definitions sheafify the actual sectionwise
  tensor and sectionwise scalar extension, with their natural maps.
- `Sheaf.CategoryTheory.ConstantCoefficientScalarExtension` (publicly imported by
  the locally-constant module dependency): `constantCoefficientRing`,
  `constantCoefficientModule`, and `constantCoefficientUnit`. The constant section
  helper is the actual module-sheafification adjunction unit applied to a constant
  presheaf, not an arbitrary selected section.

All helper declarations in the module belong to this one descent notion and are
listed in `lean.declarations`; there are no new independent notions or dependency
repairs. The module docstring names the source and every declaration carries the
item's blueprint tag. The theorem docstring carries all eleven steps of the DAG proof.
ILO XVII 7.2.3, p. 301, is read as motivation, not as a theorem for arbitrary schemes:
it assumes noetherianity. The item's explicit Stacks cover-descent proof is followed
for arbitrary connected S. XVII 7.4.6, p. 307, explicitly identifies the finite quotient
K with the Galois group of the trivializing cover and uses its module action.

Edge cases checked: empty S is excluded by ConnectedSpace; the Galois cover is
nonempty and connected by the recorded IsGalois specialization. For the identity
cover Aut c is trivial and the equivalence reduces to constant module sheaves.
The zero ring, zero modules, zero short complexes, arbitrary infinite modules,
non-noetherian coefficients, and non-flat N are allowed. Nothing divides by the
order of G; in particular its characteristic may divide that order. Site object
and arrow universes are transported by SmallModel rather than equated on S.Etale.

Searches for existing declarations:

- Retained `msearch.py` LeanFinder, 2026-10-18: "Descent of arbitrary modules along
  connected finite etale Galois cover equivalence representations exact mixed tensor";
  eight hits about cotangent spaces, Kahler differentials and etale algebras, no match.
- Retained `msearch.py` Loogle: `Rep, Action, ModuleCat`; twelve hits, including
  `Rep.ActionToRep`, `Rep.RepToAction` and their equivalence, reused here.
- Retained `msearch.py` grep: `Galois.*descent|descent.*equivalence` in CategoryTheory;
  fifteen hits in generic Sites/Descent, no module-valued Galois-cover statement.
- Current `rg` for `lem-per-galois-cover-module-descent|GaloisModuleDescent|
  galoisCoverModuleDescent` in upstream WeilConjectures and side lean/Sheaf:
  only the proof-plan reference in `Sheaf/Paper/PrimeFieldTensorDevissage.lean:114`.
- Current `rg` for `SmallModel.*Etale|smallCategorySmallModel|equivSmallModel.*Etale`
  in the same source trees: existing uses are of affine-etale generators or strict
  local neighborhoods; none defines this finite-cover descent equivalence.
- Source reads verified the complete signatures/docstrings of the recorded statement
  dependencies, and the definitions of constant coefficients, tensor functoriality,
  change of rings and Rep's monoidal/action interfaces used by the helpers.

Validation: the retained main module passed `scompile.py` cleanly before adding
proof-plan imports. The final source is recompiled and checked by deliver2 preflight.
No STATEMENT-DISPUTED finding and no statement correction.

## Second reading by Q05

This is the worker's own second pass, under the dispatcher's direct-delivery rule;
the maintainer supplies the independent review. I reread the node and the whole
Lean file, including the definitions under the theorem. Connectedness is nonempty,
G is the actual deck group, coefficients and modules are unrestricted, the essential
image is constancy on Y, and exactness is ambient rather than merely categorical
inside a possibly unrecognized abelian subcategory. The finite-type predicate is the
recorded localized-sieve definition. I checked the inverse in the deck-section
formula against contravariance, and checked both tensor morphisms in the naturality
square: scalar extension sends h by id tensor h, the N factor has trivial action,
and `mixedSheafMap` first applies f in N and then the scalar extension of T(h).
The associated mixed tensors are canonically the tensors in the node, with their
A-linear structures retained; they introduce no flatness hypothesis. No mathematical
mismatch was found. The completion added missing node/report bookkeeping and the
published proof-plan imports, and removed redundant parentheses; it supplied no proofs.
