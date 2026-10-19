## Worker report

This delivery defines `AlgebraicGeometry.ProEtale.supportedCup` in
`Sheaf.Paper.SupportedCup`. The previous tentative `existing: true` match to
`AlgebraicGeometry.Etale.cupWithSupports` was withdrawn: it has the wrong site and
coefficient normalization. No independent reading has been performed by this author.

The definition is the displayed composite in the current main-20261015 blueprint,
sec-six-functors-basics/sk-prop-a1-kummer/def-pur-supported-cup.md, with the explicit
coefficient quotient calculation in the current DAG statement. It uses fixed finite
coefficients and pro-etale sheaves throughout. No arbitrary coefficient map, arbitrary
natural isomorphism, or additional Tor hypothesis is supplied by a caller.

Clause-by-clause correspondence:

- `P : WeilConjectures.PurityFiniteSetting` fixes the field, the finite extension, and
  the positive coefficient level. The actual coefficient is `P.Coefficient`, the
  project's canonical lift of A_(E,n), and the sheaf is exactly `P.constant`.
- `{Z W X : Scheme}` and `[X.Over (Spec (CommRingCat.of P.field.k))]` express the
  ambient k-scheme. Closed immersions are the binders `i`, `j` and the two
  `IsClosedImmersion` instances. No smoothness, regularity, or finiteness is added.
- `cupIntersection i j := pullback.fst i j ≫ i` is h from the scheme-theoretic
  intersection `pullback i j`. All coefficient objects use the underived
  `lowerStar`, then `DerivedCategory.singleFunctor _ 0`.
- `F G : CupPlus P X` is exactly the existing `DerivedCategory.Plus` of the
  specified module sheaves, with the upstream localization structure shared by name.
  It expresses bounded-below inputs. `a b : ℤ`
  permits negative, zero, and positive degrees. `α` and `β` have precisely the
  supported-Hom representation specified by `supported_cohomology_hom`.
  The definition acts on representatives, as the source says, without choosing
  an unnormalized isomorphism from that theorem's `Nonempty` interface.
- `cupConstantIso` reuses the upstream canonical comparison of constant sheaves.
  `cupCoefficientRestriction` is the adjunction extension of the constant-section
  map at the base change of the terminal object. `cupCoefficientMultiplication`
  transports multiplication of the constant tensor unit. Thus both operations
  preserve the specified scalar, rather than using an arbitrary linear map.
- `cupCoefficientMap_existsUnique` specifies mu by its composite with the two
  quotient maps: restriction of the product. Those quotient maps are epimorphic,
  so this condition determines mu uniquely. `cupCoefficientMap` chooses from
  that unique characterization; it does not choose from mere existence.
- `cupCoefficientMap_isIso` and `cupCoefficient_flat` state the coefficient
  calculation attached to the node. Their docstrings give the full quotient,
  three-open-cover, idempotent, and inverse c tensor 1 arguments. The fixed-scalar
  monoidal category's `ObjectProperty.flat` is exactness of sheaf tensor, the
  flatness notion in the node, with the constant-ring action expressed by local
  scalars.
- `cupSingleTensorMap` is the actual lax tensor map of localization followed by
  the ordinary tensor comparison for complexes concentrated in degree zero.
  `cupDerivedCoefficientMap` composes this with `singleFunctor.map mu`.
  Its isomorphism theorem records degree-zero flat implies K-flat and the
  canonical localization comparison; its docstring gives that proof plan.
- `cupTensorShiftIso` moves the right shift out first, then the left shift and
  adds shifts. Its convention is (-1)^(b*r) on P[a]^r tensor Q[b]^s.
- The body of `supportedCup` calls `cupComposite`: theta inverse, followed by
  `α ⊗ₘ β`, followed by this shift isomorphism. `cupSupportedHom` defines the
  output as a Hom in `CupDerivedCategory`, with degree `a+b`. This is exactly
  the existing unbounded `ModuleDerivedCategory`, and `cupTensorObject P X` is
  the object part of the existing upstream derived tensor. There is no assumption
  that `F ⊗^L G` remains bounded below.
- `cupHasDerivedCategory P X` references the existing inferred localization
  structure. `CupDerivedCategory` and `CupPlus` transparently name the existing
  derived category and its bounded-below subcategory with that same structure
  supplied explicitly; `cupSingle` references its actual `singleFunctor 0`.
  `cupMonoidal P X := inferInstance` references the upstream canonical monoidal
  structure. `cupTensorObject` is exactly the object part of `curriedTensor`
  for that structure, hence of `derivedTensor`. These helpers share existing
  dictionaries; they introduce no new localization, resolution choice, tensor
  bifunctor, or assumptions. They are owning-node implementation helpers, not
  independent missing notions.

All postponed proof obligations belong to the coefficient calculation explicitly
included in this DAG node. Their docstrings contain complete mathematical proof
plans. The definitions contain real constructions; the only data selected using
an unproved theorem is a uniquely characterized morphism, as permitted by AGENTS §5.

Dependency declarations used directly:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `P.Coefficient`, `P.constant`.
- `Sheaf.Paper.SupportedCohomologyHom`:
  `AlgebraicGeometry.ProEtale.supported_cohomology_hom`; it imports the existing
  supported sections and bounded-below cohomology definitions.
- `WeilConjectures.SixFunctors.ProEtale.Derived.ModuleDerivedCategory`:
  `AlgebraicGeometry.ProEtale.ModuleDerivedCategory`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.lowerStar`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor` and
  `.TensorResolution`: `derivedTensor`, `laxMonoidal_Q`, and
  `derivedTensor_map_app_comp_map`, with their K-flat localization comparison.
- `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf`:
  `comparisonUpperStarConstantSheafIso` (canonical comparison, not a duplicate).
- Mathlib: `IsClosedImmersion`, scheme pullbacks and projections,
  `DerivedCategory.singleFunctor`, `singleFunctorIsoCompQ`, `constantSheafAdj`,
  `Functor.LaxMonoidal.μ`, `map₂HomologicalComplexObjSingleIso`,
  `singleMapHomologicalComplex`, `commShiftIso`, and `shiftFunctorAdd`.

The generic ringed-site tensor/flatness/K-flatness and descent dependencies explain
proofs of the coefficient calculation; their declarations were read. They are not
redefined in this module. The two record repairs below select the fixed-scalar
presentation required by the already recorded supported-Hom interface.

Edge cases checked mathematically: empty X or support gives zero coefficients;
full or identical support gives ordinary multiplication; disjoint supports give zero
intersection; nonreduced supports have the same local-constant coefficient quotient
without a reducedness hypothesis. The setting includes level n=1. Both shift signs
and arbitrary integer degrees are retained. Zero inputs give zero morphisms. Over a
finite nonfield ring such as Z/4, a derived tensor of bounded-below inputs need not
be bounded below; the output Hom convention covers this case.

Actual searches in this author run:

- `msearch.py ... leanfinder`: “cup product on pro-etale sheaf cohomology with
  intersecting closed supports using tensor of closed pushforward constant modules”.
  Eight hits on LightCondensed monoidal structures, ordinary Sheaf.H, and
  Mayer-Vietoris; none states the fixed coefficient supported cup.
- `msearch.py ... loogle`: `"Sheaf", "tensor"`. Twelve hits, including
  `PresheafOfModulesOfCommRing.Monoidal.tensorObj` and tensor morphisms; no cup.
- `msearch.py ... grep`: `cupWithSupports|supportedCup|supported_cup` in
  Mathlib/CategoryTheory. No hits.
- `msearch.py ... leansearch`: “Cup product of pro-etale sheaf cohomology classes
  with closed supports using the tensor product of closed direct images of constants”.
  Eight hits on Cartesian sheaf tensor, binaryProductExponentiable,
  HomologicalComplex.tensorObj, and condensed categories; no exact match.
- `rg` in the project and upstream source finds the etale `cupWithSupports` and
  its users. Reading its whole signature rules it out: it is not this pro-etale
  finite-coefficient construction. Searching constant-sheaf comparisons finds the
  exact upstream `comparisonUpperStarConstantSheafIso`, which is reused.

No statement correction and no new DAG node are proposed. The earlier mathematical
review obligation concerning etale versus finite pro-etale coefficients is addressed
by the actual category, coefficient sheaf, and normalized mu in this module.

## Dependency modules

`def-weil-pbc-proetale-site`: lean-only record repair. The current primary record
selects intrinsic `SheafOfModules` with a Type u ring. This consumer and the recorded
supported-Hom theorem use fixed-scalar `Sheaf ... (ModuleCat.{u+1} P.Coefficient)`.
The existing upstream `ModuleDerivedCategory` is exactly the latter localization.
It keeps site objects in u+1 and morphisms in u. No category is constructed anew.

`def-weil-derived-tensor`: lean-only record repair. The current primary record
selects an intrinsic chosen-resolution interface. The existing finite-coefficient
pro-etale `derivedTensor` is the canonical derived tensor in the fixed-scalar
category used by `supported_cohomology_hom`. Its globally supplied localization
tensor comparisons specify the K-flat normalization used here. No second tensor
functor is defined, and the coefficient and site universes remain independent in
the existing general API.

## Author recovery self-check (2026-10-17)

The required first dry run found a retained diagnostic module without a node owner.
It was preserved as CupDiagnostic.lean.txt outside the delivery module tree. The next
run confirmed a 60-second timeout in SupportedCup against current server sources.
Profiling in scratchpad exposed an actual saved-code error: the ordinary comparison
map₂HomologicalComplexObjSingleIso must be evaluated at the single complex M[0],
not at the sheaf M. This is corrected.

The degree-zero tensor comparison and right-shift-first comparison are constructed
in a general category before specialization. The helper cupDerivedCoefficientMap is the
general composite taking an ordinary coefficient morphism; supportedCup applies it only
to cupCoefficientMap P i j. The final construction is the actual composite, with no
new existence or uniqueness obligation for the cup itself.

A diagnostic compile identified repeated kernel conversion of the derived monoidal
structure as the expensive part. The final module explicitly shares the upstream
localization and monoidal instance through cupHasDerivedCategory and cupMonoidal.
The transparent CupDerivedCategory / CupPlus aliases and cupSingle / cupTensorObject
references use exactly those structures throughout. With these references, the final
cup definition passed kernel checking in 7.6 seconds in the diagnostic run (the whole
file took 11.9 seconds); that run exposed only one missing noncomputable marker and
line-length warnings, now corrected. All diagnostic options and prints remain outside
the delivery tree. No compiler timeout or heartbeat limit was raised. There is no
change to the DAG statement, hypotheses, coefficients, shift sign or output convention.

Compared all three sandbox node copies to the current shared records: only lean differs.
Re-read the current blueprint cup definition, the released C4/E4 repair note, the finite
setting and supported-Hom source, and the current server tensor/direct-image sources via
scompile.py --source where the older local checkout lacked them. In particular the
supported-Hom signature has the same PurityFiniteSetting, pro-etale site, coefficient
universe u+1, underived lowerStar, singleFunctor 0, bounded-below source and integer shifts.
The declaration uses no arbitrary coefficient comparison supplied by the caller.

Final normal scompile.py validation passed without errors or warnings for both the
isolated file (11.3 s) and the actual library module path (11.8 s), with the original
60-second limit and no diagnostic options. Exactly one Lean module is in the delivery
module tree. All three JSON copies differ from the current shared records only in lean.

The first final dry run compiled both delivered-code and existing-record checks, then
reported two signature metadata mismatches: its signature extraction starts at `def`,
excluding the preceding noncomputable modifier. The item and derived-tensor records
now use those extracted signatures; no Lean source changed for that repair.

This remains an author's self-check; the separate second reader is still required.

## Earlier second reading (a previous round; superseded)

Pending the separate independent reader requested in the worker brief. This section
records no independent approval; this packet is prepared by its author for that reader.


## Second reading by Q103

Independent second reading on 2026-10-17. I did not write this module. I opened
both blueprint versions of def-pur-supported-cup, its current main-20261015 proof,
the purity conventions and enclosing proposition, the complete sandbox node and
Lean file, the released C4/E4 repair note, and the dependency declarations. The
source of this item is a blueprint definition, not a Stacks lemma. The longer DAG
coefficient calculation supplies a site-level justification in place of the
blueprint's geometric-stalk shorthand; it does not assume geometric points are
conservative on all pro-etale sheaves.

Here is my object/hypothesis/conclusion checklist, in the order of the node.
Each item passes.

1. Fixed finite coefficient datum, base field, finite extension and n >= 1:
   `P : WeilConjectures.PurityFiniteSetting.{u}`. I read its structure, `Ring`,
   `Coefficient` and `constant`: `level_pos` is 1 <= level, the ring is the actual
   O_E/(varpi_E^n), its ULift is the established size convention, and the constant
   pro-etale module is comparison pullback of the constant etale module. No
   arbitrary torsion ring or etale replacement is introduced.
2. An arbitrary k-scheme X: `{Z W X : Scheme.{u}}` and
   `[X.Over (Spec (CommRingCat.of P.field.k))]`. Only X needs the displayed base
   structure: Z and W inherit their maps to k through i and j. There is no
   smoothness, regularity, Noetherian, separatedness or finite-type binder.
3. Closed immersions i and j: `(i : Z ⟶ X) (j : W ⟶ X)` with exactly their
   `IsClosedImmersion` instances. `cupIntersection i j` is
   `pullback.fst i j ≫ i` from the actual scheme pullback. Mathlib's base-change
   stability and multiplicativity give that this map is closed, including the
   sum-of-ideals affine model; no extra intersection hypothesis is assumed.
4. Small pro-etale site, constant A-modules and ambient unbounded derived category:
   `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)` throughout.
   `cupHasDerivedCategory` is `inferInstance`, and `CupDerivedCategory` is the
   same `DerivedCategory` with that dictionary shared explicitly. I read the
   current server source of `ModuleDerivedCategory`; these are the same objects,
   morphisms and localization, not a privately constructed derived category.
5. Underived direct images in degree zero: each coefficient object is literally
   `(lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)`, then
   embedded by `cupSingle P X`, the existing `singleFunctor _ 0`. I read the
   current `lowerStar` source: its values are sections on base change and its
   morphisms are whiskering; it is neither derived pushforward nor lower shriek.
6. Bounded-below F,G and all integer a,b: `(F G : CupPlus P X) (a b : ℤ)`.
   `CupPlus` transparently names `DerivedCategory.Plus` with the same localization.
   The input `α : cupSupportedHom P i F.obj a` (and similarly β) is exactly the
   displayed morphism representing the supported class. I read
   `supported_cohomology_hom` at lines 188ff: its source is derived pro-etale
   supported sections with this P, and its target has precisely this underived
   lowerStar, singleFunctor 0, ambient category and integer shift. The source
   expressly defines the cup after representing classes, so accepting these
   representatives does not require selecting an arbitrary comparison from the
   theorem's `Nonempty` natural-isomorphism statement.
7. The particular ordinary coefficient map μ: `cupConstantIso` uses the existing
   `comparisonUpperStarConstantSheafIso`; I read its adjunction construction.
   `cupCoefficientRestriction` adjoints the sheafification unit evaluated at the
   base-changed terminal object, hence restricts the same constant scalar.
   `cupCoefficientMultiplication` transports the constant tensor-unit unitor,
   hence multiplies scalars. `cupCoefficientMap_existsUnique` characterizes μ
   by `(q_Z ⊗ q_W) ≫ μ = multiplication ≫ q_V`. Since both q's are quotient
   epimorphisms and tensor is right exact, this uniquely specifies exactly the
   restriction-and-product map in the node. `cupCoefficientMap` selects from
   this uniqueness statement; this is permitted determined data, not a hollow
   definition or an arbitrary caller-supplied map.
8. Coefficient invertibility and flatness: `cupCoefficientMap_isIso` and
   `cupCoefficient_flat` state these facts for every closed immersion, without
   extra geometric assumptions. I read `ObjectProperty.flat`: exactness of both
   tensor functors. In this symmetric category the two exactness conditions are
   equivalent, so this is the recorded flatness notion, not a stronger
   mathematical hypothesis. Its docstring reproduces J_D, the finite list of
   coefficients, the supporting idempotent, the monomorphism argument and right
   exactness. The existence/uniqueness docstring gives the local-constant,
   quotient and three-open-cover argument for J_V=J_Z+J_W; the invertibility
   docstring gives the inverse c ↦ c tensor 1. These are the node's proof steps.
9. The specified derived θ: `cupSingleTensorMap` composes the actual lax
   monoidal localization map with the ordinary tensor comparison for single
   complexes. `cupDerivedCoefficientMap` follows it by `singleFunctor.map μ`;
   the specialization in `supportedCup` is only to `cupCoefficientMap P i j`.
   `cupDerivedCoefficientMap_isIso` has no Tor or flatness binder: its proof
   plan uses the preceding coefficient-flatness statement to make the single
   complexes K-flat, then the canonical K-flat localization comparison and μ.
   I read the current Tensor and TensorResolution server sources: this is
   exactly the published derived tensor comparison and its normalization.
10. The shift σ has sign (-1)^(b*r): `cupTensorShiftIso` first calls commShift
    for the right factor on `F⟦a⟧`, then for the left factor, then
    `(shiftFunctorAdd C a b).symm`. I checked Mathlib's
    `mapBifunctorShift₂Iso` and its component formula: moving the right shift
    multiplies by (-1)^(r*b), with r the degree in F[a]; moving the left shift
    has no sign. I also read the derived localization CommShift instances.
    The existing upstream `DerivedCategory.shiftTensorShiftIso` moves the
    left shift first and consequently differs by (-1)^(a*b); substituting it
    unchanged would fail this node's explicitly fixed convention.
11. The final operation and output: `cupComposite` is literally
    `inv θ ≫ (α ⊗ₘ β) ≫ (cupTensorShiftIso F G a b).hom`.
    `supportedCup` specializes it to the canonical θ and its named IsIso
    theorem. Its codomain `cupSupportedHom P (cupIntersection i j)
    (cupTensorObject P X F.obj G.obj) (a + b)` is exactly Hom(h_* A_V,
    (F tensor^L G)[a+b]) in the unbounded category. `cupTensorObject` unfolds
    to the same `curriedTensor` as the published `derivedTensor` definition.
    The supported-Hom theorem identifies this with supported cohomology when
    the target is bounded below. No boundedness of F tensor^L G is asserted.

Dependency-record review (H13): there are two existing-interface repairs and
no sibling dependency modules or new definition nodes. I read each dependency
node against its blueprint source and opened both its old and replacement
interfaces. `def-weil-pbc-proetale-site` formerly selected
`Scheme.proEtaleDerivedCategory`, intrinsic modules using Type u coefficients
and a standard localization; it cannot directly type the already recorded
finite-coefficient supported-Hom morphisms. Its replacement
`ProEtale.ModuleDerivedCategory` supplies exactly the fixed-scalar constant-ring
module presentation, preserving the small site. For `def-weil-derived-tensor`,
the former `Scheme.derivedTensor` takes chosen complex representatives and a
resolution in that intrinsic presentation. The replacement is the published
fixed-scalar derived bifunctor with its canonical localization maps and
left-derived characterization; tensor with the restricted constant B module
is included by taking that object as the second variable. Both notes explain
the unusable presentation and its replacement; both repairs change only lean.
The general ringed-site tensor, flatness and descent declarations are not
copied: fixed-scalar sheaves use their existing symmetric sheaf tensor, whose
local A-action extends to the constant ring sheaf by sheaf gluing.

Edge cases: empty X, empty Z or W, and disjoint supports are permitted (zero
coefficients or zero output); identical/full supports recover ordinary scalar
multiplication. Nonreduced supports are allowed and use the scheme pullback.
Zero F or G and zero representatives are allowed. Degrees a,b may be negative,
zero or positive, and the right-shift-first sign applies in every case.
n=0 is excluded already by the node's n>=1, whereas n=1 is included. The
coefficient prime differs from the characteristic through P's fixed datum;
no new characteristic restriction is added. There is no index-set binder to
exclude an empty family; the quotient proof also permits an empty finite list
(e=0). No finite-Tor condition appears. All variables and universes are bound
with autoImplicit false: schemes are in u, site objects in u+1, site morphisms
in u, and coefficient modules and derived morphisms in u+1. These site
universes are not identified. Generic implementation helpers have their own
bound c,v,w universes and specialize without extra user hypotheses.

Independent searches in this reading:

- LeanFinder: “Closed direct images of constant coefficients have a canonical
  tensor multiplication to the intersection support on the proetale site”.
  Eight hits, principally LightCondensed tensor/sheafification structures;
  none is this supported cup.
- Loogle: `"constantSheaf", "tensor"`; zero hits.
- LeanSearch: “Product of cohomology classes supported on closed subschemes
  defined by tensoring morphisms from pushforward constants”. Eight hits on
  structure-sheaf multiplication, locally constant functions, closed-immersion
  multiplicativity, tensor components and coproducts; no exact cup definition.
- msearch grep: `cupWithSupports|supportedCup|supportedProduct`; zero Mathlib
  hits. Direct rg over Mathlib, upstream WeilConjectures and project lean/Sheaf
  with these names and with `closed.*[Tt]ensor|tensor.*[Ss]upport` found the
  upstream etale `cupWithSupports` and the project's etale supported exterior
  product. I opened both: their etale sites, support adjunction objects, and
  arbitrary diagonals/exterior-product setting do not give this pro-etale
  coefficient-normalized Hom composite. The upstream name table has no binding
  for this item. Existing constant comparison and tensor/shift constituents
  are reused; the right-shift-first composite is the node's chosen convention.

No remaining object, hypothesis, quantifier, coefficient, site, sign or output
mismatch was found. No mathematical statement correction, Lean source change,
or new node was needed in this second reading. All definitions have actual
bodies; the four postponed theorems have sorry proofs and source/blueprint
proof docstrings for precisely the coefficient calculation in this node.
The complete delivered module passed the prescribed normal scompile.py checks
both in isolation (16.7 s) and at its library path (15.9 s), with no errors or
unexpected warnings. I checked all 100-character line limits and exact equality
of lean.statement with the file signature. The three node copies differ from
the shared records only in lean. This reading changes the review report only.
