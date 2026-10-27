## Worker report

The module `Sheaf.Algebra.Homology.TensorDoubleHomExactComparisons` states
`DerivedCategory.tensor_double_hom_exact_comparisons`, with its whole proof `sorry`.
It supplies the exactness, coherent integer shifts, canonical representative
normalizations, and signed tensor-cone comparison of the node. No definitions are
introduced, and the node is changed only in `lean`.

The source passages read are `more-algebra.tex`, lemma-derived-tor-exact (064J),
and `sites-cohomology.tex`, lemma-RHom-triangulated (08JC), together with all six
steps of this node's accepted signed expansion. The source leaves the Hom
triangle calculation as details omitted; the node's explicit signed calculation
is included in the declaration's proof docstring. This is stage 2: nothing is
proved here.

The prior failure concerned a stage-1 re-splitting gate, because Q74 had already
split and reviewed this node. That acceptance did not attach a Lean declaration.
This delivery performs stage 2 and preserves the accepted statement, proof,
dependencies, split report, and review fields. No repair note is present for this
item. The earlier sandbox was empty.

Hypotheses and clauses, matched with Lean:

- The commutative ring is `(R : Type u) [CommRing R]`. Ordinary R-modules are the
  existing `CategoryTheory.RingSiteModules R`, on
  `CochainComplex.onePointRingSheaf R` and the bottom topology of the discrete
  singleton category. The existing category presents every R-module, including
  the zero ring, without a topological or finiteness restriction.
- The ambient category is `DerivedCategory (RingSiteModules R)`, with its recorded
  `HasDerivedCategory.{u}` size convention. The first conjunct quantifies over
  every `L M` of this category, independently. Its tensor functor is
  `tensorLeft ((SignedRingedHom.hom ... L).obj M)`. This is F, using the recorded
  internal Hom and native K-flat derived tensor, not a newly chosen tensor.
- G is written directly as the composite of the `rightOp` of the contravariant
  Hom-into-L functor and the contravariant Hom-into-M functor. Each is
  `(Functor.curry.obj (SignedRingedHom.homFunctor ...)).flip.obj` at its target.
  Its object is exactly RHom(RHom(K,L),M), with its prescribed action on maps.
- Exactness is `Functor.IsTriangulated` for both functors. Tensor uses the
  already existing signed `CommShift` instance. G has an existential
  `Functor.CommShift ℤ`; its fields include naturality and the zero/addition
  coherence laws. Its comparison is equated to the signed composite of the two
  existing `SignedRingedHom.sourceShift` maps, with the `m.negOnePow` scalar
  and the canonical `neg_neg m` reindexing. These clauses apply to every integer,
  including negative shifts, and every derived K.
- The representative part quantifies over arbitrary complexes `J I` with
  separate `[J.IsKInjective] [I.IsKInjective]`. It writes L=QJ, M=QI in
  representative coordinates. This is the node's choice of representatives,
  not a restriction on its initial arbitrary L,M: the first conjunct already
  covers all L,M, and the representative comparison transports along their
  chosen isomorphisms. There is no equality J=I or L=M.
- A is the existing `homComplex J I`, always with the original ring sheaf as
  its explicit R argument. No K-flatness of A is required.
- `s U V m` has exactly the type Hom(U[m],V) ≅ Hom(U,V)[-m]. Its product-projection
  equation, using `homComplexπ`, source and output `shiftFunctorObjXIso`, and
  `(m*q).negOnePow`, says precisely that it reindexes source components and
  multiplies a degree-q homogeneous map by (-1)^(m*q). The equation is an
  equality of module-sheaf morphisms, including all local sections.
- `repJ` and `repI` are canonical representative isomorphisms: their hom maps
  are required to equal Q applied to Hom of the fixed
  `CochainComplex.toKInjectiveResolution` augmentation, followed by the inverse
  `WeilConjectures.coefficientHomResolutionIso` localization factorization.
  They are not unconstrained representative identifications.
- `tensorRep P hP` identifies Q Tot(A⊗P) with F(QP) for every K-flat P. Its
  defining equation says that precomposing with `Functor.LaxMonoidal.μ Q A P`
  is `(repI J).hom ⊗ₘ 𝟙 (Q.obj P)`. Thus it is the canonical derived tensor
  comparison, even though A need not itself be K-flat or have flat terms.
- `homRep P` identifies Q Hom(Hom(P,J),I) with G(QP), for every complex P.
  Its hom is required to be `repI (homComplex P J)` followed by the Hom map
  induced contravariantly by `(repJ P).inv`. Only I, not Hom(P,J), is assumed
  K-injective. This explicitly fixes the canonical double-Hom identification.
- `chi P m` is the representative double-Hom shift. Its hom is required to be
  `m.negOnePow` times Hom into I applied to `(s P J m).inv`, followed by
  `s (homComplex P J) I (-m)` and the canonical double-negation shift transport.
  This is the displayed ψ formula, with composition read in Lean's diagrammatic
  order. In particular the leading factor (-1)^m has not been omitted.
- The tensor representative shift square equates localization of
  `TotalTensorSigns.shiftLeft A P m`, followed by the localization shift and
  shifted `tensorRep`, with `tensorRep` at P[m], the image of the localization
  shift, and the actual derived tensor comparison. `shiftLeft` is exactly
  `CochainComplex.mapBifunctorShift₂Iso`: its documented component formula
  (`ι_mapBifunctorShift₂Iso_hom_f`) is multiplication by `(a*m).negOnePow` on
  the summand of first degree a. This fixes φ's required (-1)^(m*a) formula.
  Both `hP` and `hmP` are supplied for the corresponding K-flat representatives;
  this does not impose another hypothesis on K, since K-flat shifts remain
  K-flat by the recorded total-tensor result.
- The corresponding Hom representative shift square equates localization of
  `chi` with the actual G comparison through the fixed `homRep`. Thus the
  derived ψ and its chain formula are the same comparison, rather than two
  independently asserted shift isomorphisms.
- For every map f:P₁→P₂ between K-flat complexes, the cone is the existing
  `CochainComplex.mappingCone f`. The comparison is the actual
  `TotalTensorSigns.coneLeft A f`, an isomorphism by its definition, not an
  arbitrary morphism. The first equation fixes the unshifted component and cone
  inclusion. The following `ι` equation fixes the shifted component to
  `a.negOnePow` times the target's shifted-summand inclusion. Together these
  give exactly h⊗(y,x) ↦ (h⊗y,(-1)^a h⊗x), in Mathlib's summand order.
- The last equation compares `mappingCone.triangle f |>.mor₃` on both sides
  after `TotalTensorSigns.shiftLeft ... 1`. Mathlib's mor₃ is the negative cone
  projection, so this is precisely the required negative connecting arrow,
  not the unsigned projection. Combined with the tensor shift square, it is
  the boundary equation after φ at shift one.
- G's exactness is stated for this same normalized comparison. The proof
  docstring describes the two contravariant reversals, restriction to the
  mixed (J,I) block of the existing single-target result, and its boundary
  equation. No boundedness, perfectness, flatness of the Hom complex, equality
  of targets, or K-injectivity of the intermediate Hom is assumed.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, and Q's shift structure.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses` and its representative comparisons.
  `SignedRingedHom.homFunctor` specializes this same recorded declaration.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `mapBifunctorShift₂Iso`, its summand equation, and the coherent `CommShift₂Int`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (unfolded to check its test
  against every acyclic complex and its use of the original sheaf tensor).
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, the node's `mathlib_match`.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`; `HomComplexComponents` supplies their fixed product
  projections and differential/action formulas.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `.Functor`:
  `Pretriangulated`, `Functor.CommShift`, `Functor.IsTriangulated`, the recorded
  triangulated-category and exact-functor interface.
- The existing helper modules `RingHomExtensionDefs`,
  `RingedInternalHomSignedCalculus`, and `CoefficientHomRepresentativeEvaluation` provide
  `RingSiteModules`, `SignedRingedHom.homFunctor`, `.hom`, `.sourceShift`, the
  native derived tensor and its localization structure, and
  `coefficientHomResolutionIso`. The representative maps are written as direct
  composites of the existing augmentation, Hom functor, localization functor,
  and inverse factorization; no comparison definition is duplicated. The
  downstream `DerivedEvaluationCanonicalMap` module is deliberately not
  imported: F and G are written directly from the recorded bifunctor, avoiding
  an import cycle when the evaluation theorem later uses this item.
- Proof imports retain the recorded modules for
  `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`,
  `exists_isKFlatResolutionIndependentCoefficients`,
  `kFlat_fixed_tensor_triangulated`, `totalTensorHomotopyConeSigns`,
  `SignedDoubleHomCone.comparison`, `quasiIso_homComplex_map`, and
  `mappingCone.quasiIso_iff_acyclic`. The cone and shift names appearing in
  the signature are publicly imported; modules needed only for the future proof
  have ordinary imports.

Edge cases checked before finalizing: the zero ring, zero J or I, zero P, zero
map f, identity map f, arbitrary unbounded complexes, distinct targets J and I,
shifts 0, 1, -1 and inverse shifts m+(-m)=0, and characteristic two. The Hom
sign is a unit in ℤ acting additively, so it also specializes correctly in
characteristic two. At m=0 the displayed comparisons are identities; at m=1
χ has its required leading minus, and the tensor's shifted cone summand has
(-1)^a. The node's proof gives the sign exponent m(n+c) for χ; substituting
m=1 yields the known mixed-target cone sign. All parameters and universes are
explicit; `autoImplicit` is false.

Searches for an existing exact statement:

- `msearch.py`, LeanFinder: "Derived tensor and double derived Hom with different
  targets are exact with signed integer shift and cone comparisons". Eight hits
  on homological-functor exact sequences and derived single triangles; no match
  with this normalization and two independently chosen Hom targets.
- `msearch.py`, Loogle: "Functor.CommShift, Functor.IsTriangulated,
  CochainComplex.mapBifunctorShift₂Iso". No hits; the service did not recognize
  the unqualified `Functor.CommShift` identifier. The exact Mathlib signatures
  were instead opened directly in their recorded files.
- `msearch.py`, grep of Mathlib CategoryTheory:
  "doubleHom|DoubleHom|double_hom|evaluationDoubleHomShift". No hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the prescribed
  `grep -rn` for the item id in `lean/WeilConjectures`: no existing declaration
  carrying the item. The broader name search finds the downstream evaluation
  theorem's definitions and its exactness clause, but it does not state this
  node's fixed representative maps, s formula, φ representative square, and
  tensor-cone component/boundary normalization. The single-target
  `SignedDoubleHomCone.comparison` does not state the two-target derived result.
  All the reusable lower-level constructions found by these searches are used.

No statement dispute or correction. No new nodes or dependency repairs.

Validation: every compile uses the prescribed `scompile.py`, in module mode,
against the live published build. Initial elaboration diagnostics were repaired
by specifying the actual site/coefficient universes in Hom and homObjMap calls;
no universe equality, extra mathematical hypothesis, or enlarged file timeout
was introduced. The final compile and delivery dry run are recorded below.

Final explicit `scompile.py` result: success, no errors or warnings; sandbox
14.8 seconds and library 22.1 seconds, both within the unchanged 60-second limit.

Preflight repair: the first dry run refused a direct import of
`RingedSiteDualityMaps`, attached to route-pivot-dropped
`def-per-ringed-site-bidual-transpose`. Removed that import entirely. Both
representative normalization equations now directly compose the active
`toKInjectiveResolution`, `homComplexFunctor`, `Q`, and
`coefficientHomResolutionIso`, with exactly the same augmentation and
localization factorization. This neither imports a dropped module through a
re-export nor introduces a substitute definition or unconstrained map.

After removing the dropped-module import, the complete final module compiled
cleanly again through `scompile.py`: sandbox 13.6 seconds; library 7.5 seconds.
The node's recorded signature was refreshed verbatim from this version.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
