## Worker report

The module `Sheaf.AlgebraicGeometry.NormalReflexiveOpenEquivalence` states
`AlgebraicGeometry.Scheme.Modules.normal_reflexive_open_equivalence`.
Its only proof is `by sorry`; it defines no objects and changes only the item's `lean` field.
The original statement, statement dependencies, proof, and proof dependencies are unchanged.

Source read: `literature/stacks-project/divisors.tex`, lemma-reflexive-S2-extend,
Tag 0EBJ, including its proof; `properties.tex`, lemma-criterion-normal, Tag 0345.
The node specializes 0EBJ's boundary depth assumption to normality and local dimension
at least two, using Serre's criterion. This specialization is retained, rather than
replacing the node by the more general depth version.

Hypothesis and clause correspondence:

- Integral scheme Y: `{Y V : Scheme.{u}} [IsIntegral Y]`. Mathlib's integral class
  includes nonemptiness and integral domains of sections on nonempty opens.
- Locally Noetherian: `[IsLocallyNoetherian Y]`, with no global Noetherian or
  quasi-compact assumption.
- Normal: `hnormal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)`.
  Integral Y already makes every stalk an integral domain. Thus this is exactly
  normality, expressed using the normal-domain clause of def-weil-pbc-normal-ring.
- Open subscheme j: `(j : V ⟶ Y) [IsOpenImmersion j]`. An arbitrary open immersion
  is allowed, including presentations other than a chosen `Y.Opens` object.
- Local dimension at the omitted points: `hcodim : ∀ y : Y, y ∉ Set.range j →
  (2 : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)`.
  The complement is the complement of the image of j, and the dimension is that
  of the specified local ring, not the dimension of the scheme or the open.
- Modules and all their morphisms: `Y.Modules`, `V.Modules`, and their ordinary
  category-theoretic arrows. No restriction is placed on module morphisms.
- Coherent: `RingedSpace.IsCoherent Y.toRingedSpace F` (and its V analogue).
  This is the finite-type plus finite-type-kernels definition, not just a
  private quasi-coherent-finite-type replacement.
- Reflexive: `IsIso (SheafOfModules.bidual (R := Y.sheaf) F)` (and its V analogue).
  The existing bidual morphism has target
  `homObj (homObj F (unit _)) (unit _)` and sends a section to evaluation at it.
  Thus the actual evaluation map must be invertible, not merely some map or some
  isomorphism between F and its double dual. No reflexivity predicate is redefined.
- Restriction preserves the subcategory: the first quantified conjunct asserts both
  `IsCoherent` and invertibility of bidual for `(restrictFunctor j).obj F` whenever
  F is coherent reflexive.
- Canonical unit for F: that same conjunct asserts
  `IsIso ((restrictAdjunction j).unit.app F)`.
- Direct image preserves the subcategory: the second quantified conjunct asserts
  `IsCoherent` and invertibility of bidual for `(pushforward j).obj G` whenever
  G is coherent reflexive on V.
- Canonical counit for G: that same conjunct asserts
  `IsIso ((restrictAdjunction j).counit.app G)`.
- Quasi-inverse equivalence: these two preservation clauses let the actual functors
  restrict to the full subcategories of coherent reflexive modules. Their existing
  natural unit and counit have invertible components there. This is precisely the
  canonical unit/counit formulation of their being quasi-inverse equivalences;
  it supplies both directions and imposes no choices of replacement functors.
- Hom bijection: the final conjunct quantifies over two arbitrary coherent reflexive
  objects and asserts `Function.Bijective
  (fun f : F₁ ⟶ F₂ ↦ (restrictFunctor j).map f)`. It refers to the actual restriction
  map on every Hom set.

Dependency declarations read and used:

- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- def-weil-pbc-normal-ring: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with the integral-domain part provided by integral Y.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : ... → WithBot ℕ∞`.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly exposing
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The dependency record now explicitly
  lists this exact coherence predicate in addition to its preserved older conjunction.
- def-pur-sheaf-hom:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, `SheafOfModules.homObj`.
  The existing evaluation constructor is `SheafOfModules.bidual` from the sibling
  upstream module `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual`.
- def-pc-module-pullback: publicly import its recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, with
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and the upstream
  tensor pullback. Since j is open, the statement uses Mathlib's actual restriction
  `restrictFunctor`, `pushforward`, and `restrictAdjunction` from
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`. The source explicitly supplies
  `restrictFunctorIsoPullback`. This does not introduce a replacement pullback,
  direct image, adjunction, unit, or counit.

All ten already recorded non-statement proof-dependency modules are privately imported:
DepthTwoHartogsRestriction, CoherentLocalFinitePresentation,
CoherentModuleLocalOnOpenCover, CoherentSheafHom, ModuleFinitePresentationExtension,
NormalLocalDepthTwo, QuasicoherentFiniteTypeAffine, StalkInternalHomFinitePresentation,
DualDepthTwo, and CoherentFiniteTypeLocallyNoetherian (their full upstream paths are
in the module). The node's five proof steps are written out in the theorem docstring,
including the coherent dual/stalk-Hom argument, affine finite-presentation extension,
explicit reflexive hull, and the extension formula on Hom sets. The three newer
statement-only proof inputs (affine-reflexive-module-comparison, coherent-reflexive-hull,
noetherian-open-immersion-qc) have no recorded modules in the read DAG and therefore
have no imports; they are proof inputs, not missing notions in this signature.

Edge cases checked against the source and signature:

- j an identity/isomorphism: the complement condition is vacuous and both canonical
  adjunction maps are isomorphisms; restriction gives the expected Hom bijection.
- Zero coherent module: its evaluation is invertible, and zero maps/Hom sets are
  included. The proof's depth convention is infinity for the zero module.
- Empty Y: excluded by the original integral hypothesis, not by a new binder.
- Empty V: allowed as a scheme and open immersion in the signature. For an integral
  Y the local-dimension hypothesis cannot then hold at its generic point (dimension
  zero). No unjustified nonempty-V hypothesis has been added.
- In dimension zero or one, no point with local dimension below two can be omitted.
  Singular normal schemes in larger dimension remain covered; regularity and local
  freeness of F or G are not imposed.
- Non-quasi-compact Y and V: no extra compactness or separation assumptions occur;
  the proof uses only affine-local extension. The arbitrary universe u is explicit,
  and module sections use the project's usual scheme-module size convention.

Searches (2026-10-24):

- msearch.py leanfinder, query: "Restriction across codimension two on a locally
  Noetherian normal integral scheme is an equivalence of coherent reflexive sheaves".
  Eight hits: normalizationDiagram, instIsIsoToNormalizationOfIsIntegralHom,
  Opens.instIsIsoCommRingCatAppLEιTopToScheme, ι_toNormalization,
  toNormalization_app_preimage, ofRestrict_appIso, ι_fromNormalization_assoc,
  exists_eq_pow_mul_of_is_compact_of_quasi_separated_space_aux. None states the theorem.
- msearch.py loogle, query: "IsReflexive, IsCoherent". Zero hits; unknown unqualified
  identifier IsReflexive. No matching sheaf-extension result.
- msearch.py grep, query: "reflexive|reflexivity|codimension", AlgebraicGeometry.
  Three hits in AlgebraicCycle/Basic and OrderOfVanishing, all unrelated.
- msearch.py leansearch, query: "Coherent reflexive sheaves extend uniquely across
  codimension two in a normal locally Noetherian integral scheme". Eight hits on
  hom_ext_iff, presentation constructors, OpenCover.ext_elem, finite-presentation
  quasi-coherence, and IsQuasicoherent; none supplies reflexive extension.
- rg on lean/WeilConjectures and lean/Sheaf for reflexive, Reflexive, doubleDual,
  dualEval, bidual, and reflexive-S2-extend found the existing internal Hom and bidual
  API and the finite-locally-free/invertible biduality results. These are reused;
  none gives extension of arbitrary coherent reflexive modules. The exact item-id
  search in lean/WeilConjectures returned no match.
- The same searches found no existing `normal_reflexive_open_equivalence` declaration.

No new nodes, dependency repairs, statement corrections, or disputed statements are needed.

Validation: scompile.py compiled this single file on the server in both sandbox and
library module mode with no errors or warnings (2.5 s and 2.6 s). No direct Lean,
Lake, global build, repository mutation, or git command was run by the worker.

## Second reading by Q138

This is a second pass by the same worker, not an independent-agent review: the dispatcher
explicitly forbids starting other agents, and the maintainer performs the independent
review. Reopened the original JSON and the final module. Checked Y's integral and
locally Noetherian binders, normality at every stalk, the actual image complement,
and the numerical lower bound on local Krull dimension. Checked the two coherent and
bidual hypotheses on each side, restriction preservation, direct-image preservation,
the exact canonical unit and counit, and the restriction map on all Hom sets. The
canonical unit/counit form is equivalent to the stated equivalence of full categories,
including both object preservation directions. Checked that `bidual` is evaluation
into sheaf Hom twice rather than tensor evaluation. No mismatch was found and no
statement was changed. There are no extra modules or nodes to review.
