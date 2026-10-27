## Worker report

Stage 2 statement of `lem-sfb-space-module-flattening-by-admissible-blowup` (Stacks
Tag 087C, `spaces-more-morphisms.tex`, theorem-flatten-module, lines 8777–8854).
Read the source theorem and proof and the strict-transform definition in
`spaces-divisors.tex`, Tag 0862, lines 3940–3980. No source-based correction is needed.
The accepted stage-1 split and every proof dependency are unchanged. The inherited
BLOCKED ending concerned an unchanged stage-1 delivery: the current item is queued
at stage 2, has no Lean record, and the standing brief §0 explicitly authorizes this
handoff. No repair note for this item is present.

The theorem is
`AlgebraicGeometry.AlgebraicSpace.exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleFlatteningByAdmissibleBlowup`.
Its only proof is `sorry`. The new definition module contains a real structure
and no postponed theorem or data choice.

Clause-by-clause correspondence:

- Scheme S and algebraic spaces over S: `{S : Scheme.{u}}` and
  `(X T U XU : AlgebraicSpace S)`. The one explicit universe u follows the existing
  algebraic-space interface: schemes and section/ring carriers are u-small; its big
  and small etale site objects are in u+1. No independent size equality is imposed.
- The open U of T: `j : U ⟶ T` and `hj`, representability by scheme open immersions.
  Giving an open immersion instead of a subfunctor represents the same open with
  its embedding. It permits the whole open, the empty open, and any isomorphic model.
- `X_U = X ×_T U`: `fU`, `qU`, and `hU : IsPullback qU.hom fU.hom f.hom j.hom`.
  This gives an actual cartesian square of sheaves; its choices are isomorphic to
  the sheaf fibre product. No representability or separation is assumed of f.
- T quasi-compact: `hTqc` is exactly a scheme `V : Over S` with compact underlying
  space and a representable etale, surjective atlas to T.
- T quasi-separated: `hTqs : IsAbsolutelyQuasiSeparated T`, the existing absolute
  affine-test diagonal criterion. It does not assume the base S quasi-separated.
- U quasi-compact: `hUqc` is the same compact-scheme atlas criterion for U.
- X quasi-compact: `hXqc` is the same atlas criterion for X.
- f locally of finite presentation: `hflfp : MapIsLocallyOfFinitePresentation f`,
  the existing test on every compatible pair of etale scheme charts.
- M is a quasi-coherent O_X-module: `(M : X.Modules)` and `hMqc : M.IsQuasicoherent`.
  This is the existing small-etale ringed-site module category and Mathlib's local
  presentation predicate, with the recorded slice instances.
- M finite type: `hMft : M.IsFiniteType`, Mathlib's locally finite generation predicate.
- M_U finite presentation: `hMUfp` uses Mathlib `SheafOfModules.IsFinitePresentation`
  on `(moduleTensorPullback qU).obj M`. This is the canonical restriction to X_U,
  expressed by tensor pullback along the actual cartesian projection.
- M_U flat over U: `hMUflat : ModuleIsFlatOver fU ...`. The recorded definition tests
  every compatible source and target etale chart and uses the scheme `IsFlatOver`
  on the restricted Zariski module. For these quasi-coherent modules its affine-local
  condition is equivalent to the stalk condition stipulated by the item. It includes
  charts of X_U ×_U A: these are compatible source-target chart diagrams, and conversely
  a compatible diagram factors through that fibre product.
- Existential centre: `∃ I : QuasiCoherentIdeal T`, with
  `(I.val : T.Modules).IsFiniteType`. Quasi-coherence and actual inclusion into O_T
  are part of the existing subtype, rather than added assumptions on an arbitrary map.
- `I|_U = O_U`: for every etale chart V of T admitting a factorization through j,
  `idealSectionImage I.val.arrow V = ⊤`. These tests express exactly the unit ideal
  on U, including on nonaffine charts; the inclusion is a submodule sheaf inclusion.
- The actual blowup: `B : BlowupPresentation I`. Its etale affine charts are the
  ordinary scheme blowups of the restricted ideal, with their projection and cartesian
  squares; this specifies the descended relative Rees Proj up to isomorphism over T.
  The finite-type centre I is retained. The scheme `def-nagata-global-blowup` remains
  the chartwise blowup construction, used through that existing space presentation.
- The ambient product and strict-transform quotient: `D : ModuleStrictTransformPresentation
  f I B M` retains its `ambient`, `toSource`, `toBlowup`, `cartesian`, `module`,
  `quotient`, `epi`, and full `kernel` equivalence. This is a quotient with specified
  kernel, not an arbitrary module, map or unnormalized choice. Its torsion condition
  is expanded below in the new-node discussion. The item describes the space transform
  as explanatory setup; the theorem concerns the module transform and does not require
  an additional space-transform conclusion.
- M' finite presentation as an O_(X ×_T T')-module:
  `SheafOfModules.IsFinitePresentation D.module`. This also implies quasi-coherence.
- M' flat over T': `ModuleIsFlatOver D.toBlowup D.module`, the identical chartwise
  relative-flatness predicate used in the hypothesis over U.
- No quasi-separatedness of f (or X), no Noetherian hypothesis, no representability
  of f, no separatedness, and no extra flatness of f occur in the signature.

Dependency declarations read and used (including each original statement dependency):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  locally ringed spaces locally affine and their locally ringed morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`, `Modules`; the fppf sheaf
  and representable diagonal/atlas definition and the full small-site interface were read.
- `def-weil-size-convention` is a recorded metatheoretic convention with no declaration;
  its explicit-universe requirement is implemented by `universe u`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
  Their full signatures and proof docstrings were read; the module is publicly imported.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`, the all-compatible-chart tests.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  the closed embedding and surjective-on-stalks class. The module is publicly imported
  as an original statement dependency; the target conclusion is a module quotient.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, the recorded locally
  ringed space open-immersion predicate, used by hj.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its slice
  sheafification instances; the underlying predicate is Mathlib
  `SheafOfModules.IsQuasicoherent`. Its local-presentation definition was read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `ModuleDirectImageModel`,
  `moduleTensorPullback`, `moduleTensorAdjunction`. Read the chart-section limit model,
  normalization, and left adjoint defining canonical tensor pullback.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, the glued scheme
  blowup, and `blowupMap`; read their definitions. Space blowups are expressed using
  the already-landed `BlowupPresentation` below, not by applying this scheme def to a space.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`; read the full affine-local definition and stalkwise
  equivalence docstring. It is used by `ModuleIsFlatOver` after scheme restriction.
- Added existing definition-node citations (no changes to these dependency nodes):
  `def-sfb-space-flat-proper-coefficient` owns `ModuleIsFlatOver`, in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`;
  `def-sfb-space-absolute-quasi-separated` owns `IsAbsolutelyQuasiSeparated`, in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`;
  `def-sfb-space-blowup-presentation` owns `BlowupPresentation` and `IdealIsUnitAbove`,
  in `Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation`;
  `def-sfb-space-quasi-coherent-ideal` owns `QuasiCoherentIdeal` and `idealTensorMap`,
  in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal`;
  `def-sfb-space-ideal-power-products` owns `idealSectionImage`, already defined in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees`. These declarations and docstrings
  were read and reused. The new definition owns only the missing module quotient model.

All original statement-dependency modules are public imports. All currently stated
proof-dependency modules are also imported (plain import when used only in the proof).
The seven proof steps in the theorem docstring preserve the accepted split, including
quasi-compactness of the pulled-back open, product-centre refinement, the flat tensor
comparison of torsion kernels, and passage from covering charts to all charts.
Unstated proof lemmas have no module to import yet; no proof import cycle was introduced.

Edge cases checked before writing:

- U=T and I=O_T: the blowup is the identity; its exceptional equation is a unit,
  so only the zero section is power torsion, and the module transform is M.
  The hypotheses already give finite presentation and flatness.
- U empty: the two restricted-module hypotheses concern the empty fibre product
  and impose no global condition. The centre condition is vacuous away from empty tests;
  zero ideal centres and empty blowups are permitted, as in the source.
- X empty and/or T empty: empty scheme atlases are permitted; compactness does not
  imply nonemptiness. The cartesian squares and quotient presentations allow empty spaces.
- M=0: the quotient is zero and flat and finitely presented; no nonzero module is required.
- Nilpotent centre: a zero/empty blowup or a section killed by a positive ideal power
  is allowed. No reduction, integrality or regularity of X is silently imposed.
- Exponent n=0: J^0 is the full ring, so annihilation forces the restricted section
  to be zero. Every further restriction is tested, including identities. Positive
  exponents handle genuine torsion. Covering sieves allow locally different exponents.
- Non-quasi-separated X: no source diagonal condition occurs. Absolute quasi-separatedness
  is required only of T, exactly as in Tag 087C.

Searches for existing declarations:

- `msearch.py leanfinder`: "Flatten a finite type quasi coherent module on an algebraic
  space by admissible blowup; strict transform is quotient of tensor pullback by
  exceptional divisor power torsion". Eight hits: flatness of affine-section maps,
  normalization diagrams, scheme image and quotient lifts; no space flattening theorem
  or space module strict-transform definition.
- `msearch.py leansearch`: "Strict transform of a module sheaf is its pullback modulo
  sections locally killed by powers of an ideal". Eight hits: scheme tilde/pullback,
  restrictions, free pullback isomorphism, scheme ideal map; no exact match.
- `msearch.py loogle`: `"strictTransform"`, zero hits.
- `msearch.py grep`: `strictTransform|StrictTransform|flattening|flatification`,
  Mathlib AlgebraicGeometry, zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for transform, flattening, and the intended names: existing scheme theorem
  `AlgebraicGeometry.exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup`
  applies to schemes, and `SpaceFlatteningByAdmissibleBlowup` transforms spaces.
  Neither states the current theorem in namespace `AlgebraicGeometry.AlgebraicSpace`.
  `grep -rn` of the item id in WeilConjectures returned no hit.
- DAG grep for module strict transforms: the existing definition
  `def-trf-module-strict-transform` is scheme-only. The space-transform-presentation
  node treats the structure-sheaf torsion ideal and a closed space, not a general module
  quotient. The localization lemmas mention module quotients without defining their data.
- `tools/blueprint_refs.py search "module strict transform"` returned zero blueprint
  nodes; `ancestor` for this item is the inherited null ancestor. The new node keeps
  that exact ancestor and extends its via chain. The new-node mathlib_searches retain
  the actual msearch results (including returned names, counts and digest).

Validation: both delivered files compiled individually in dependency order through
`scompile.py NP lem-sfb-space-module-flattening-by-admissible-blowup`, against the
live published library. No errors or unaccepted warnings. No local/global build,
no direct repository edit and no direct git command was used.

## New nodes

`def-sfb-space-module-strict-transform-presentation` (Tag 0862(1)) defines
`AlgebraicGeometry.AlgebraicSpace.ModuleStrictTransformPresentation` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStrictTransformPresentation`.
It consists of the ambient cartesian square, module N, quotient epimorphism from
q^*M, and its exact exceptional-ideal torsion kernel. Epi and this kernel specify
the quotient up to its unique isomorphism commuting with the quotient map. Thus the
existential transform in the theorem cannot be an arbitrary module chosen to satisfy
the conclusions. No object is chosen and no data is postponed. For a finite-type
centre and quasi-coherent input, this is the source strict transform; the structure
also makes sense for arbitrary modules by the same kernel characterization.

For every V and s, `D.kernel V s` gives both directions of the defining equivalence.
The witness `R ∈ ambient.etaleTopology V` is a covering sieve; its arrows a index local
restrictions; `∃ n : ℕ` allows a local exponent. The quantifiers over Z, b and r in
`idealSectionImage (idealTensorMap (toBlowup ≫ B.projection) I) Z ^ n` express that
this power of the pulled-back centre ideal sheaf annihilates the restricted section.
This uses the actual canonical tensor-ideal map; it does not assume that sections on
nonaffine tests generate the sheaf. On affine localizations where the exceptional ideal
is (t), the condition is exactly t-power torsion. This includes all locally supported
sections in the definition preceding Tag 0862 and retains the centre I.

The underlying notions are the already-existing algebraic spaces, sheaf fibre products,
module pullback, quasi-coherent ideals, blowup presentations and ideal-section images.
All are cited in the definition node; no duplicate copy is introduced. The searches
above show why scheme module transforms and space structure-module kernels do not
supply this missing notion. The new node belongs to the item's chapter/unit and cites
exactly the ids used by its self-contained statement. The item's only changes are its
Lean record and added definition dependencies; its natural-language statement is intact.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review, head 14059473)

Group O4 (lem-sfb-space-strict-transform-etale-localization, head 6432eca7, PASS) delivered
the same new node `def-sfb-space-module-strict-transform-presentation`, in the same module
path and with the same declaration name, in parallel with this delivery. In O4's version the
ambient fibre product is supplied by a parameter `P : StrictTransformPresentation f K B`
(the landed space strict-transform presentation, `def-sfb-space-strict-transform-presentation`),
and the structure carries only `module`, `quotient`, `epi` and the identical kernel rule.
Landing this delivery's copy would overwrite that node. The two notions agree: the
ambient square of this copy is exactly the first four fields of `StrictTransformPresentation`,
and such a presentation of the space strict transform always exists, so quantifying over
it in the conclusion changes nothing.

The fix drops this delivery's copy of the new node (`--drop-nodes
def-sfb-space-module-strict-transform-presentation`; the item keeps the citation, which
names O4's landed node) and restates the conclusion as
`∃ (B : BlowupPresentation I) (P : StrictTransformPresentation f I B)
(D : ModuleStrictTransformPresentation f I B P M), IsFinitePresentation D.module ∧
ModuleIsFlatOver P.toBlowup D.module`. The item module compiles against O4's text of the
definition module (`nt_compile.py --json`, both files clean).
