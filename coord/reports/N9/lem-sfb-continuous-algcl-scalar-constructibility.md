## Worker report

Stage 2, group N9, item lem-sfb-continuous-algcl-scalar-constructibility.
The module Sheaf.Paper.ContinuousAlgclScalarConstructibility states
AlgebraicGeometry.ProEtale.ContinuousAlgclScalar.scalar_constructibility.
Its only postponed proof is that theorem, with the complete seven-step reviewed
DAG proof in its docstring. Every helper has concrete data or is an application
of an already published structural construction. No new nodes, dependency
repairs, mathematical corrections, or disputed statements are needed.

The earlier worker's blocker concerned stage-1 re-splitting a reviewed node.
This task is stage 2: the reviewed node has no Lean record, and the delivery
adds only that record, its statement module, and this report. Its statement,
proof, dependencies, split report, and maintainer review are unchanged.
There is no released repair note for this item.

### Hypotheses, objects, and every conclusion

- The prime ell is `ℓ : ℕ` with `[Fact ℓ.Prime]`. The field Q_ell is
  `Padic ℓ`, the recorded Mathlib completion of the rationals.
- The algebraic closure is `Ω : Type u`, `[NormedField Ω]`,
  `[Algebra (Padic ℓ) Ω]`, and `[IsAlgClosure (Padic ℓ) Ω]`.
  `hNorm` says explicitly that its norm extends the ell-adic norm.
  Its topology is the topology of that norm. There is no completeness binder.
- The finite intermediate field is literally `E : IntermediateField (Padic ℓ) Ω`,
  with `[FiniteDimensional (Padic ℓ) E]`. Its norm and topology are the
  inherited subtype norm and topology; its actual inclusion is `E.val`.
- `k : Type u`, `[Field k]`, `p : ℕ`, `[CharP k p]`, `hp : p.Prime`, and
  `hpℓ : p ≠ ℓ` render the positive characteristic different from ell.
  For a field, positive characteristic is necessarily prime, so this is
  equivalent to the stated positive-characteristic hypothesis.
- `T : Scheme.{u}` with structure map `t : T ⟶ Spec (CommRingCat.of k)` and
  `[IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]` is precisely a
  separated finite-type k-scheme. No restrictions are put on the schemes
  occurring as pro-etale covering members.
- `Profinite.continuousCoefficientRingObj E` and the analogous Ω object have
  sections `ULift C(P,E)` and `ULift C(P,Ω)` for every profinite P. The ULift
  changes only the universe. These include ALL continuous functions, with
  no finite-subextension or locally constant replacement. They are
  definitionally the recorded `continuousMapRingObjOfUniverse.{u,u}` objects:
  a sandbox equality with proof `rfl` compiled through scompile.py.
- `inclusion` wraps the recorded `continuousMapRingObjMapOfUniverse` applied to
  `E.val.toRingHom` and `continuous_subtype_val`. Its underlying component is
  precisely postcomposition. The ring compatibility term is the existing
  `Sheaf.isMonHom_sheafCompose_map`, for the recorded sheaf map. No ring
  map is postulated. `coefficientInclusion` is its image under
  `(upperStarFromPoint X).mapMon`, i.e. the required A_{E,X} → B_X.
- `M` lives in `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T)
  Ab.{u+1}) (condensedRingObj A T))`, the ordinary UNBOUNDED derived category
  of the recorded internal module category, with A the continuous E ring.
  `hM : constantModelBoundedConstructible A T M` uses the recorded bounded
  finite-constant-cohomology predicate, rather than the distinct ambient
  locally-finitely-presented constructibility predicate.
- Integers `r s`, `hrs : r ≤ s`, and `hAmplitude` assert exactly that the
  homology objects are zero for `q < r ∨ s < q`.
- `scalarExtension` is the existing `Mod.extendScalars` for the actual
  coefficient map, followed by the existing total `leftDerivedFunctor`.
  The first conclusion is `constantModelBoundedConstructible B T` of its
  value on M. The second conclusion is the same `IsZero` condition on
  homology outside the SAME interval [r,s].
- The third conclusion supplies `S : Scheme.FiniteLocallyClosedStratification T`
  and `∀ a, Topology.IsConstructible (S.stratum a)`. The recorded structure
  supplies finiteness, locally closed strata, disjointness, coverage, actual
  scheme domains, and immersion maps with exactly those images.
- The existential family `D : ℤ → Scheme.FiniteLocallyClosedStratification T`
  gives adapted stratifications for EVERY cohomology module of M, including
  the zero cohomology outside the interval. Each D has constructible strata;
  its adaptedness is the recorded `HasFiniteConstantLocalModel` applied to
  the exact module restriction of `H^q(M)` along its immersion. The clause
  `∀ q a, ∃ b, S.stratum a ⊆ (D q).stratum b` is precisely simultaneous
  refinement, with the usual set-containment meaning. No predetermined
  arbitrary family of stratifications is added as a hypothesis.
- For each S-stratum the conclusion gives a genuine
  `Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a)`. Its members
  `C.X i` and maps `C.f i` are the required W_ai → T_a.
- On each member there is ONE complex P over `scalarRingObj A`, the scalar
  ring A(*) from the recorded local-model definition. Ordinary modules are
  encoded as `Mod Ab (scalarRingObj A)`. Evaluation of continuous functions
  on the one-point profinite set identifies that ring canonically with E,
  with its ordinary algebraic ring structure. This is the dependency's
  prescribed encoding of E-vector spaces; it is not a new vector-space
  notion. `Mod.IsFree (scalarRingObj A) (P.X q)` means that the term is
  isomorphic to E^n for some NATURAL n (see ModuleObjects.Free), hence is
  exactly finite dimensionality, including dimension zero. The further
  `IsZero (P.X q)` outside [r,s] makes P a bounded complex in that interval.
- `scalarModel A W P` first uses `(scalarConstant W).mapMod` termwise on P,
  then `DerivedCategory.Q`, then the existing total derived extension along
  `scalarCoefficientHom A W`. Thus it is exactly
  A_W tensor^L_{discrete constant E} discrete constant P. The action comes
  from the recorded constant-section counit. `scalarConstant` is the
  recorded constant sheaf on the point followed by inverse image, and its
  recorded `scalarConstant_iso_constantSheaf` identifies it with the actual
  discrete constant sheaf on W. It never replaces underlines by continuous
  coefficient sheaves.
- The first `Nonempty` iso is in the A_W internal-module derived category:
  the restriction of M along `C.f i ≫ S.immersion a` is isomorphic to the
  above scalarModel. Restriction is the recorded
  `CondensedRing.moduleObjectDerivedPullback`; its ordinary inverse-image
  interpretation follows from the exactness and coefficient-ring
  normalization explained in proof step 1.
- `scalarInclusion` is the image of the SAME continuous coefficient inclusion
  under `scalarSections.mapMon`. Under one-point evaluation it is E → Ω.
  Applying `Mod.extendScalars` for this map termwise to the SAME P therefore
  gives Ω tensor_E P with differential 1 tensor d. The final `Nonempty` iso
  is in the B_W internal-module derived category and identifies restriction
  of the scalar extension of M with `scalarModel B W` of this termwise
  scalar-extended complex. Both requested isomorphisms are on derived
  objects, not merely their separate cohomology groups.

### Dependency declarations read and used

- Mathlib.NumberTheory.Padics.PadicNumbers: `Padic` and its norm/topology.
- Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure and Basic:
  `AlgebraicClosure`, `IsAlgClosure`, with algebraicity and algebraic
  closedness; the statement allows any fixed closure, not only the
  canonical constructed representative.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  the standing separated finite-type-over-a-field convention and
  `CondensedRing.compactificationOverField` signature. No compactification
  is required for the scalar operation; its setting is rendered explicitly.
- Sheaf.Topology.ContinuousMapCondensedRing:
  `Profinite.continuousMapRingSheafOfUniverse` and
  `Profinite.continuousMapRingObjOfUniverse`.
- Sheaf.Topology.ContinuousMapCondensedRingMap:
  `Profinite.continuousMapRingSheafMapOfUniverse` and
  `Profinite.continuousMapRingObjMapOfUniverse`, including their section
  formula and ring-compatibility statement. The concrete canonical ring
  structure uses the published global tensor interface. The same coefficient
  sheaf is also exposed by ContinuousCoefficientUniverse and
  ContinuousCoefficientCommRing; their alias is definitionally equal at
  the universes used here, as checked by the compiled consumer probe.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  `coefficientRing`, `upperStarFromPoint`, `condensedRingObj`,
  `isCommMonObj_condensedRingObj`. The map specialization is the published
  `coefficientMap` from ChangeOfCoefficients, equivalently mapMon's hom.
- Mathlib.CategoryTheory.Monoidal.Mod: `CategoryTheory.Mod` and its action
  and compatible-morphism structures, instantiated on abelian sheaves.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions:
  the recorded derived-category convention interface; actual ambient
  objects are the same Mathlib `DerivedCategory` localization at quasi-isos.
- WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars:
  `Mod.extendScalars`, `Functor.leftDerivedFunctor`,
  `Mod.derivedExtendMapDerivedCategoryAdjunction` and its K-flat convention.
- Sheaf.Paper.CondensedConstantConstructibility:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`.
- Sheaf.AlgebraicGeometry.FiniteConstantLocalModel:
  `scalarSections`, `scalarRingObj`, `scalarConstant`,
  `scalarConstant_iso_constantSheaf`, `scalarCoefficientHom`,
  `finiteConstantScalarExtension`, `HasFiniteConstantLocalModelOnCover`,
  and `finiteConstantLocalModel_iff_exists_cover`.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`,
  `constantSheafAdj`, as used by the recorded scalarConstant construction.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, its topology,
  and `Scheme.proetalePrecoverage` and covering families.
- Sheaf.Paper.CondensedModuleDerivedPushpull:
  `CondensedRing.moduleObjectDerivedPullback`, used without imposing
  finite-type hypotheses on a covering member.

The recorded statement dependency modules are public imports. Every already
stated proof prerequisite is imported without public; this includes the
internal/section tensor and scalar comparisons, internal inverse-image
comparison, exact abelian upper star, common refinement of strata and covers,
pro-etale inverse image and object/slice restriction, internal kernels and
cokernels, sheaf tensor, and common-stratification exactness. Mathlib
Noetherianity, immersion/permanence, and locally-surjective-epi inputs are
also imported. `lem-sfb-internal-scalar-pullback-normalization` has no recorded
Lean module yet, so there is no module to import for that proof prerequisite.
It is not a missing notion in the present statement.

### Edge cases checked

Empty T admits the zero-stratum partition; D can have zero strata in every
degree, and all covering/model demands over S are vacuous. No Nonempty or
positive-n hypothesis excludes this case. For M = 0 the chosen complexes
can all be zero, using rank-zero finite free terms; no nonzero-rank condition
is present. When r = s the term-vanishing clause leaves only that degree.
Internal zero objects, rather than equality to a chosen zero carrier, render
zero terms categorically. Individual zero terms and empty strata are allowed.
E = Q_ell is allowed by the bottom intermediate field. Pro-etale cover
members have no finite-type, quasi-compact, or separated binders. Ω need not
be complete. There is no flatness assumption on B_T as an arbitrary A_T-module.

The source was read locally: HRS PDF, Section 3 (Example 3.1, Remark 3.2,
Definitions 3.3 and 3.5 and scalar preservation paragraph), and the current
blueprint direct-images statement/proof, clause (3). The reviewed node
supplies the explicit cohomology-based finite-free cycle-lifting argument,
so no general t-exactness of scalar change on arbitrary modules is inferred.
The full proof is retained in the theorem docstring.

### Searches

- msearch.py leanfinder: "Derived extension of continuous algebraic closure
  field coefficients preserves bounded constructible cohomology and finite
  constant local complex models". Eight unrelated hits, including continuous
  group cohomology, algebraic closure embeddings and scalar restriction;
  no matching theorem.
- msearch.py loogle: `"DerivedCategory", "IsGE"`. Twelve hits, including
  `DerivedCategory.IsGE`, `isGE_iff`, and bounded representative lemmas;
  these express abstract cohomological bounds, not the present scalar and
  constructibility statement.
- msearch.py grep: `constructible.*(extendScalars|scalar)|scalar.*constructible`
  in Mathlib/CategoryTheory. Zero hits.
- msearch.py leansearch: "Derived scalar extension of continuous coefficient
  sheaves has finite constant local complex models with the same cohomological
  interval". Eight unrelated hits concerning continuous linear scalar
  restriction and light condensed objects; no exact match.
- rg in lean/WeilConjectures and lean/Sheaf for the item ID: no declaration.
  Concept search for continuous scalar extension and constructibility found
  the existing finite/adic/colimit-coefficient results, not the requested
  all-continuous algebraic-closure norm topology with both local derived
  models. In particular the upstream ModuleObject.Colimit.TwoColimit uses
  the colimit-coefficient construction, not the present norm coefficient ring.
- rg for `scalarCoefficientHom.*leftDerived`,
  `leftDerivedFunctor.*scalarCoefficientHom`,
  `scalarConstant.*mapHomologicalComplex`, and
  `finiteConstantScalarExtension.*leftDerived` in the project: zero hits.
  The helper scalarModel simply composes the recorded constant mapMod,
  localization, and derived scalar extension, with no new independent notion.
- rg for intermediate/subfield normed-field instances found
  SubfieldClass.toNormedField. A scompile probe synthesized the inherited
  NormedField E. The module uses that structure and continuous_subtype_val.

## Second reading by N9

The dispatcher expressly forbids starting another agent. This section records
this worker's second pass against the node and delivered file; the maintainer's
independent delivery review remains independent, and no second agent is claimed.

I reread the full node statement and every conjunct of scalar_constructibility.
The two coefficient sheaves use actual continuous norm-topology functions.
The characteristic, algebraic-closure/norm-extension, finite-intermediate-field,
and separated finite-type hypotheses all have explicit counterparts. The
cohomological interval is unchanged, the common stratification has actual
scheme immersion data and constructible images, and its family D explicitly
records adaptedness and simultaneous refinement. The local models share the
same P and the second uses its actual termwise scalar extension. Both are
derived isomorphisms. No ambient-module flatness or completeness has entered.

During elaboration I replaced an unregistered map-ring compatibility inference
by the existing concrete Mon.Hom proof, exposed colimit preservation from the
existing composite adjunction to form termwise constant module complexes, and
removed a duplicate algebraic-closure instance binder reported by the linter.
These are interface/instance elaboration repairs, not changes to the mathematics.
All helpers merely name canonical composites or existing structural instances.
No mismatch with the reviewed natural-language statement remains.
