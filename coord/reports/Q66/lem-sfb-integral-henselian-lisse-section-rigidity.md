## Worker report

The module `Sheaf.Paper.IntegralHenselianLisseSectionRigidity` states
`AlgebraicGeometry.ProEtale.CondensedRing.integral_henselian_lisse_section_rigidity`.
Its only theorem has proof `sorry`. Three auxiliary declarations give real data:
the extended tensor ideal, the quotient spectrum map, and the tensor projection.
There are no new nodes, dependency repairs or statement corrections. The item's
node is changed only in `lean`; all four declarations are listed there.

The previous worker's stale-assignment diagnosis confused a stage-1 review with
a stage-2 statement review. The current node has `reviewed` for Q100's split,
but no `lean` or `reviewed_lean` record. The stage-2 statement is still needed.
The source was read in HRS arXiv:2305.18131v1, Section 4.1 and Section 4.2:
Corollary 4.4(1) gives the unconditional actual component map, while the
w-strict extension and the unit-normalized section map come from the already
recorded component-cohomology node, as the item's source explicitly specifies.
This is not asserted to be a verbatim theorem of HRS.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Arbitrary commutative rings A, B, C | `(A B C : Type u)` and three `CommRing` instances. |
| Unital maps A -> B, A -> C | `[Algebra A B] [Algebra A C]`; these encode arbitrary unital maps, without injectivity. |
| Ideal I of A | `(I : Ideal A)`. |
| B integral over A, every element satisfying a monic polynomial | `[Algebra.IsIntegral A B]`, Mathlib's elementwise integrality class. |
| C w-contractible | `[IsWContractibleRing C]`, the recorded upstream class. |
| (C,IC) henselian | `[HenselianRing C (I.map (algebraMap A C))]`. |
| D = B tensor_A C | The actual Mathlib tensor product `B ⊗[A] C`, throughout. |
| ID = (IC)D | `integralHenselianTensorIdeal A B C I = I.map (algebraMap A (B ⊗[A] C))`. `Ideal.map_map` and `Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap` identify this with extension of IC by includeRight. |
| T = Spec D and T0 = Spec(D/ID) | The endpoints of `integralHenselianClosedFibre A B C I`, constructed using `Spec` and the actual ideal quotient. |
| a is the quotient closed immersion | `integralHenselianClosedFibre` is exactly `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ...))`; no arbitrary closed immersion is supplied. |
| b is the projection to Spec B | `integralHenselianTensorProjection` is exactly Spec of `Algebra.TensorProduct.includeLeft.toRingHom`. |
| D integral over C | First conjunct: `.toRingHom.IsIntegral` on the actual `includeRight : C →ₐ[A] B ⊗[A] C`. This avoids choosing an ambiguous right tensor Algebra instance and states precisely integrality of the canonical C-map. |
| (D,ID) henselian | Second conjunct, `HenselianRing (B ⊗[A] C) (integralHenselianTensorIdeal A B C I)`. |
| D and D/ID w-strictly local | Third and fourth conjuncts, the two `IsWStrictlyLocalRing` predicates. |
| Actual pi0(a) a homeomorphism with quotient topology | Fifth conjunct, `IsHomeomorph (integralHenselianClosedFibre A B C I).continuous.connectedComponentsMap`. Mathlib `ConnectedComponents` has its quotient topology; this is the actual induced continuous map. |
| Every commutative condensed ring, not just a continuous-function model | Universal quantifier over `Profinite.CondensedRing.{u}`, with `[IsCommMonObj Λ.X]`. |
| Lambda_Y = p_Y^* Lambda on the small pro-etale site | `condensedRingObj Λ.X Y`, the underlying object of the recorded `coefficientRing`, and `Sheaf (Scheme.ProEt.topology Y) Ab.{u+1}`. |
| Internal module L on Spec B | `L : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of B))) Ab.{u+1}) (condensedRingObj Λ.X (Spec (.of B)))`. |
| L finite-rank lisse, rank zero and varying ranks permitted | `IsLisseCoefficientModule Λ.X L`; read its definition: a pro-etale cover, with `Mod.IsFree` at every member. That predicate is `∃ n : ℕ, Nonempty (M ≅ finiteFree R n)`. |
| M = b*L finite-rank lisse | First conjunct after the lisseness implication: `IsLisseCoefficientModule Λ.X ((upperStar Λ.X (integralHenselianTensorProjection A B C)).obj L)`. |
| Canonical restriction RΓ(T,M[0]) -> RΓ(T0,a*M[0]) invertible in D(Ab) | Last conjunct, `IsIso ((componentLisseSectionsPullback Λ (integralHenselianClosedFibre A B C I)).app ((upperStar Λ.X (integralHenselianTensorProjection A B C)).obj L))`. |
| Actual unit followed by canonical derived composition comparison | The imported definition `componentLisseSectionsPullback` is the degree-zero restriction of `componentDerivedSectionsPullback`, whose body is the actual `derivedUpperStarLowerStarAdjunction` unit followed by `componentModuleDerivedSectionsLowerStarIso`. Its target is normalized by `singleFunctorCompLeftDerivedFunctorIso`. |
| Ordinary unbounded derived categories, K-injective RΓ, forgetting scalars | That same map uses `(condensedModuleSections Λ.X Y).rightDerivedFunctor` into `DerivedCategory Ab.{u+1}`; sections are terminal evaluation with the internal-module action forgotten. No completion or boundedness is imposed. |
| Compatible size convention | One ambient explicit universe `u` contains all three rings and spectra; profinite tests and schemes are at `u`, abelian coefficients at `u+1`, and their small pro-etale sites have their published object and morphism universes. There is no equality of site object/morphism universes imposed. |
| No additional finiteness, Noetherianity or restrictions on coefficients | None appears among the binders. The conclusion does not claim w-contractibility of D. |

Dependency declarations used (their recorded modules, with no private copies):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj` and their
  coefficient comparison. These are publicly reexported by the sections module.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and `ModObj`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`, and the
  reexported `derivedUpperStarLowerStarAdjunction`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`
  and the reexported `IsWLocalRing`, `IsWStrictlyLocalRing` hierarchy.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: reexported `HenselianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  the constructed quotient Spec map is its canonical example.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`; the component quotient type
  and topology are Mathlib's existing `ConnectedComponents`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `IsLisseCoefficientModule`, using the existing `Mod.IsFree` from
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`.
- `def-weil-size-convention` is the recorded metatheoretic convention and has
  no declaration to import.
- `Sheaf.Paper.WStrictLisseComponentCohomology` supplies the exact existing
  `componentLisseSectionsPullback`, read with all its defining comparisons,
  and `wstrict_lisse_component_cohomology` for the proof plan.

Every stated proof-dependency module is imported: integral base change,
integral-over-henselian-pair, affine qcqs, tilde sections, affine inclusion,
integral algebra approximation, quasi-coherent algebra colimits, ind-finite
w-strict locality, henselian w-strict locality invariance, condensed henselian
rigidity, profinite point pullback, lisse definitions and component cohomology.
The theorem docstring follows all five DAG steps and names these nodes.

Edge cases checked before writing:

- B or C the zero algebra: tensor algebra is zero, spectra and component
  spaces are empty; no `Nontrivial`, `Nonempty` or chosen point is required.
- I = 0: the quotient map is canonically the identity situation, not excluded.
- I = A: the henselian Jacobson-radical condition forces C = 0, already allowed.
- Arbitrary infinite integral B/A and noninjective ring maps: no finite,
  finite-presentation or injectivity hypothesis occurs. Approximation maps in
  the proof plan are explicitly allowed to be noninjective.
- Rank zero and different local finite ranks: the recorded local `∃ n : ℕ`
  includes zero and is quantified separately at every cover member.
- Arbitrary condensed coefficients, including the zero ring and coefficients
  without completeness or discreteness: no extra property is used in the type.
- No extremal disconnectedness is asserted for the tensor algebra's components.

Searches for existing statements:

- `msearch.py ... leanfinder`: “Integral algebra over a henselian weakly
  contractible ring has weakly strictly local spectrum and lisse condensed
  module derived sections invariant under henselian quotient”. Eight hits,
  including `BDeRham`, `BDeRhamPlus`, `HenselianLocalRing`,
  `IsAdicComplete.henselianRing`, `PreTilt.exists_smodEq_untiltAux`,
  `HenselianLocalRing.toIsLocalRing`, `HenselianRing`, and
  `instHenselianRingMaximalIdeal`; none states this tensor-algebra section result.
- `msearch.py ... leansearch`: “Derived sections of lisse condensed modules on
  integral algebras over henselian weakly contractible rings are invariant under
  quotient by the henselian ideal”. Eight hits: `CondensedMod.isDiscrete_tfae`,
  `CondensedMod.isDiscrete_iff_isDiscrete_forget`, `instAbelianCondensedMod`,
  `instHenselianRingMaximalIdeal`, `CondensedMod.LocallyConstant.adjunction`,
  `CondensedMod.LocallyConstant.functorIsoDiscreteComponents`,
  `CondensedMod.IsSolid.mk`, and
  `CondensedMod.LocallyConstant.fullyFaithfulFunctor`. None is the integral
  henselian pro-etale section-rigidity statement.
- `msearch.py ... loogle '"HenselianRing", "IsIntegral"'`: zero hits.
- `msearch.py ... grep '(wStrict|WStrict|wContract|WContract).*(lisse|Lisse|integral|Integral)'`:
  zero Mathlib hits.
- `rg` with that pattern in `lean/WeilConjectures` and `lean/Sheaf` finds
  references to the existing w-contractible lisse evaluation module, and the
  component-cohomology and henselian-rigidity modules. Their full signatures
  were read: neither states the tensor-algebra integrality and geometry
  together with this section assertion. They are reused, not restated.
- Exact node-id and prospective declaration-name searches in both Lean roots
  find no existing declaration for this item. The only nearby theorem names
  are `wstrict_lisse_component_cohomology` and `henselian_lisse_rigidity`.
- Read the finite-free predicate and coefficient-ring constructors to verify
  rank-zero and arbitrary-condensed-coefficient cases instead of introducing
  replacement definitions.

Validation: `scompile.py` compiled the file in both sandbox and library module
contexts, in 12.1 and 11.4 seconds respectively, with no errors or non-sorry
warnings. The node signature is copied verbatim from the theorem, with every
variable and universe explicitly bound. No statement dispute or node fault
was found.

The prescribed delivery dry run passed preflight and per-file compilation.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
