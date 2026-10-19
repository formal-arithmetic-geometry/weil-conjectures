## Worker report

`Sheaf.Paper.PurityExteriorProductFrame` states
`WeilConjectures.PurityFiniteSetting.exteriorProduct_frame`, with `sorry` as
its proof. Its helper definitions construct the actual ordered boundary class,
projection pullbacks, supported cup, and specified pro-etale exterior class.
The delivery includes the missing induced pairing on individual supported
classes as `def-pur-supported-exterior-classes`. Both nodes cite the already
landed definition node
`def-pur-supported-class-operations` for the canonical operations. The
functoriality theorem remains only a proof dependency. There is no statement
correction and no dependency-module repair.

The hypothesis and clause correspondence is:

- `P : PurityFiniteSetting` supplies exactly the finite-field datum k, ell,
  finite extension E and positive coefficient level n. `P.Coefficient` is
  the existing size lift of A_{E,n}. There is no ramification-divisibility
  hypothesis.
- `aX`, `aY` give the two k-scheme structures; `SmoothOfRelativeDimension dX aX`
  and its Y counterpart give smoothness with constant dimensions. `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` give separated finite type. The
  dimensions dX and dY are independent of each other and of the coefficient level.
- `i`, `j` with `IsClosedImmersion` give the specified closed immersions;
  `Smooth (i ≫ aX)` and `Smooth (j ≫ aY)` give smoothness of their sources.
  `_hc` and `_hd` express pure codimension by the exact pointwise stalk
  Krull-dimension convention of `def-pur-frame-class`. Natural-number
  codimensions include zero.
- `f : Fin c → Γ(X, ⊤)` and `g : Fin d → Γ(Y, ⊤)` are the ordered tuples.
  `ef`, `hf`, `eg`, `hg` identify their scheme-theoretic zero subschemes with
  Z and W over the ambient schemes. Thus they generate the ideal sheaves,
  rather than merely cutting out the underlying closed sets.
- `pullback aX aY` is the ambient product and
  `pullback (i ≫ aX) (j ≫ aY)` is Q. The immersion is precisely the published
  `Etale.supportedProductImmersion`. `_hQ` is the assumed pure codimension c+d.
- `exteriorFrameTuple` concatenates the two global-function pullbacks by
  `Fin.addCases`, with the first tuple before the second. The witnesses
  `eh`, `hh` assert scheme-theoretic ideal generation on the product.
  `e`, `he` identify Q with the intersection of the actual two projection
  pullbacks of the closed immersions. These isomorphisms over the ambient
  scheme are uniquely determined because the immersions are monic; they
  are conclusion witnesses, not extra hypotheses.
- `exteriorFrameClass` uses the existing `frameBoundaryProduct` directly,
  precomposed with the single-complex image of `frameClosedCoefficientIso`.
  This is the specified ordered left-associated Kummer-boundary product.
  The recorded `frameClass` wrapper ties its relative dimension to P.level;
  the recorded general `frameBoundaryProduct` avoids imposing that unrelated
  restriction here. There is no second frame-class construction.
- `exteriorFrameCup` uses `functorialCupPullback` along the two projections,
  with their actual Cartesian squares; it then uses `functorialCup true`,
  the published supported cup followed by the normalized twist product.
  `functorialCupChangeSupport` identifies the intersection presentation with Q.
- `exteriorFrameExternal` first uses the normalized
  `supportedCoefficientDerivedAdjunction` to transpose each Hom class to a
  map from A[0] into supported sections of its shifted twist. `exteriorFrameUnit`
  is the canonical map A[0] → A[0] tensor A[0]. Tensor the two transposed maps,
  apply exactly `supportedExteriorProductOverField` to the unshifted coefficient
  objects, apply supported sections to `exteriorFrameTarget`, and transpose
  back under the same adjunction. `exteriorFrameSupportIso` supplies the
  canonical single-complex and constant-coefficient comparisons on each source.
- `exteriorFrameCoefficientMap` composes the derived-inverse-image comparison
  with exact inverse image, its degree-zero single-complex comparison and the
  root-normalized twist pullback. `exteriorFrameTarget` specializes this map
  to the normalized twist multiplication. Its source is the actual
  `externalProduct`, the native tensor of the two derived projection pullbacks.
  `exteriorFrameTensorTarget` applies the published right-shift-first
  `cupTensorShiftIso` to the scalar-module transposes. The supported sections
  shift comparison moves the two source shifts out and the result shift back.
  The published `supportedExternalProduct_eq` transports the explicit tensor
  presentation into the external product. This is the canonical coefficient
  identification into A(r+s)[a+b].
- The theorem's conjunction is exactly the two equalities in the displayed
  three-term chain. The documented helper `exteriorFrameReindex` only transports 2c+2d=2(c+d) and
  the natural-number cast of c+d. Hence all classes lie in the same supported
  Hom model of H_Q^{2(c+d)}(P,A(c+d)).
- For an empty tuple the existing boundary fold uses `frameEmptyClass`, the
  supported unit. The theorem includes either and both empty tuples. It
  asserts no frame independence, gluing, or identification with smooth purity.

Dependency declarations read and used:

- `Sheaf.Paper.PurityConventions` and `Sheaf.Paper.PurityFiniteSetting`:
  the finite coefficient datum `WeilConjectures.PurityFiniteSetting`, its
  `Coefficient` and `constant`.
- `Sheaf.Paper.PurityFrameClass`: `frameBoundaryProduct`, `frameTwist`,
  `frameClosedCoefficientIso`, and its empty and successor constructions.
- `Sheaf.Paper.SupportedCup`: `cupSupportedHom`, `cupSingle`, `cupConstantIso`,
  `cupSingleTensorMap`, `cupTensorShiftIso`, and `cupIntersection`.
- `Sheaf.Paper.SupportedCupFunctoriality`: `FunctorialCupH`, `functorialCup`,
  `functorialCupPullback`, `functorialCupTwistPullback`,
  `functorialCupTwistProduct`, `functorialCupChangeSupport`,
  and the shared single/derived-category instances. These definitions are
  owned by `def-pur-supported-class-operations`; the theorem node is not
  needed to state either delivered declaration.
- `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct`:
  `supportedCoefficients`, `supportedCoefficientDerivedAdjunction`,
  `supportedSectionsDerived`, `supportedExteriorProductOverField`, and
  `Etale.supportedProductImmersion` from its imported etale module.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExternalProduct`:
  `AlgebraicGeometry.ProEtale.externalProduct`; its current source was read
  with `scompile.py --source`. It is the tensor of the two derived projection
  inverse images, exactly as used by `exteriorFrameTarget`.
- `Sheaf.Paper.SupportedHomAdjunctionTranspose`: the normalized Hom/adjunction
  convention and `supportedHomCoefficientFinite`. `exteriorFrameScalarHasDerived`
  names `HasDerivedCategory.ofIsGrothendieckAbelian` for the same module category.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`:
  `DerivedCategory.singleFunctorObjUnitIso`.
- Mathlib's `Smooth`, `SmoothOfRelativeDimension`, `IsClosedImmersion`,
  relative-dimension base change and composition, and scheme pullbacks.
  `Sheaf.Paper.SupportedHomPullback` is imported for proof Steps 4 and 5.

The edge cases checked are c=0, d=0, both zero, empty supports and ambient
schemes, arbitrary independent ambient dimensions and coefficient level,
ramified coefficient levels, and every universe u with the required u+1
coefficient lift. Local Noetherianity follows from finite type over the field
and is installed from that theorem, not imposed as an additional hypothesis.
There is no STATEMENT-DISPUTED finding.

The retained searches in `searches.jsonl` are:

- msearch leanfinder: “The supported class of a concatenated frame is the cup
  product of pulled back frame classes and the exterior product”: eight
  unrelated frame and finitely supported-function results, no match.
- msearch loogle: `"supportedCup", "frameClass"`: zero hits.
- msearch grep: `frameClass|supportedExteriorProduct`: zero Mathlib hits.
- msearch leansearch: “Cup product of supported Kummer frame classes under a
  product of schemes”: eight unrelated scheme coproduct/order-frame results.
- rg of upstream WeilConjectures and side lean/Sheaf for `frameClass`,
  `exterior_product_frame`, `exteriorProductFrame` and the node id found
  the existing frame constructions and frame independence, but no matching
  product-frame theorem. `dag/lean_names_upstream.json` has no matching entry.
  The resumed reading again checked both source trees for the helper names.

## New nodes

`def-pur-supported-exterior-classes` defines the induced pairing on individual
supported cohomology classes with integer degrees and twists, using the
specified pro-etale derived exterior map. Its source is Step 5 of the
main-20261015 blueprint proof of `sk-thm-regular`, which uses exactly this
pairing on frame classes. The existing
`def-pur-proetale-supported-exterior-product` defines the derived map kappa,
whose inputs are coefficient objects; it does not define its induced pairing
on individual Hom representatives, including the coefficient and shift
identifications. The new node supplies this notion and is cited by the item.
Its module is `Sheaf.Paper.SupportedExteriorClasses`, and its main declaration
is `WeilConjectures.PurityFiniteSetting.exteriorFrameExternal`.

Every new-node hypothesis is explicit: `P` is the finite datum, `aX`, `aY`
are the scheme structures with `LocallyOfFiniteType`, and `i`, `j` are closed
immersions. The four arbitrary integers are `a b r s`; the two supported Hom
classes are `alpha` and `beta` (written α and β). Its output has product
support, degree `a+b`, and twist `r+s`. `exteriorFrameSupportIso` supplies the
normalized constant-single comparison, and `exteriorFrameTranspose` uses the
published supported adjunction. `exteriorFrameUnit` carries 1 to 1 tensor 1.
`exteriorFrameTensorTarget` applies the right-shift-first comparison;
`exteriorFramePairing` moves the output shift back past supported sections
and transposes under the product-support adjunction. The argument γ to this
pairing is precisely `supportedExteriorProductOverField` followed by supported
sections of the normalized coefficient map. The helper
`exteriorFrameProjectionCoefficientMap` constructs the same coefficient map
on the published `derivedTensor` presentation before transport through
`supportedExternalProduct_eq`; no new tensor or exterior map is selected.
All helpers contain real composites; there is no postponed data or new theorem.

The retained new-node search records include LeanFinder (eight unrelated
group-cohomology results), Loogle (`"supportedExteriorProduct"`, zero hits),
Mathlib grep (`supported.*[Ee]xterior|[Ee]xterior.*[Cc]lass`, zero hits), and
LeanSearch (eight exterior-algebra results). DAG/blueprint and source/side
searches distinguish the existing derived kappa from the missing induced
class pairing. Their raw records are included in the new node's
`mathlib_searches`. Empty supports, empty schemes, zero and negative degrees
and twists are permitted by this definition. Locally Noetherian instances
are obtained from local finite type over the field, not additional assumptions.

## Dependency modules

None. The unnecessary `PurityFrameClass` speed-up and its node record have
been removed as requested, preserving NV's landed interface. Both delivered
modules compile against the live `PurityFrameClass` through their imports.

## Second reading by NR

This is the dispatcher's required self-check, not an independent-agent review;
the dispatcher forbids starting other agents and the maintainer independently
reviews delivery. I opened the current item, its recorded dependencies, both
delivered modules, and Step 5 of the main-20261015 blueprint proof.

The hypothesis map in Worker report covers every binder and conclusion:
independent ambient dimensions and coefficient level, separated finite type,
closed smooth sources, all three pure-codimension conditions, ordered global
functions with scheme-theoretic ideal generation, the product tuple and
product support, and both equalities with the specified products. The
existential support isomorphisms are conclusion witnesses, not assumptions.
Natural-number codimensions include zero; the existing empty fold gives the
unit. No mathematical mismatch or statement correction was found.

The first resumed dry run timed out in SupportedExteriorClasses; current-source
server confirmation reproduced it. The retained profiler diagnostics locate
costly kernel comparisons in exteriorFrameCoefficientMap and exteriorFrameExternal.
The repair builds the same comparison on the published derivedTensor
presentation and transports by the existing supportedExternalProduct_eq;
its general composites are defined before specializing schemes. All helper
names are recorded in the new node's lean.declarations. Development profiling
and heartbeat settings were removed from the delivered source. The item
signature is unchanged except that its two equality casts now use the
documented `exteriorFrameReindex` helper instead of `functorialCupReindex`.
The helper is the same bare `ha ▸ hr ▸ α` construction, and the node
`lean.statement` is copied verbatim from the updated file. The theorem proof
is sorry.

## Returned-delivery repair

H2 is repaired: the item's statement dependencies replace the theorem
`lem-pur-supported-cup-functoriality` with the existing definition node
`def-pur-supported-class-operations`. The new exterior-classes node makes
the same replacement in its statement text and statement dependencies.
I read that node's full record and the existing operations in
`Sheaf.Paper.SupportedCupFunctoriality`; its 26 declarations own the Hom
model, cup, pullback, change of support, single, source and twist maps used.
The only unowned operation, reindexing, is replaced by a documented helper
in the item's module and recorded in its `lean.declarations`. No new theorem
or mathematical assumption is introduced. The natural-language item statement,
proof and proof dependencies are unchanged. The frame-class dependency's
relative-dimension/level issue is avoided exactly as in the reviewed packet
by using its existing `frameBoundaryProduct`, without changing its record.

The saved packet first passed a dry run (32b66433eb), before this repair.
The repaired two-module packet compiled cleanly through `scompile.py`:
SupportedExteriorClasses 51.2 s as sandbox / 42.9 s as library, and
PurityExteriorProductFrame 16.9 s as sandbox / 15.8 s as library. There were
no errors or warnings; the original 60-second per-file limit is unchanged.
Both node signatures match their source verbatim. Every delivered Lean line
is at most 100 characters; autoImplicit is false and universes are explicit.
The item changes only lean and stmt_deps; proof_deps and proof text are
unchanged. The new node has the corrected definition-owner citations in both
its statement and stmt_deps, and there is no frame dependency file in the
packet. The empty-tuple and independent-dimension checks still apply.
