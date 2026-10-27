## Worker report

The module `Sheaf.RingTheory.NormalizationAlgebraicTransitionSystem` states
`Algebra.NormalizationTransition.normalization_algebraic_transition_system`.
All theorem bodies are `sorry`; all definitions have actual data. No node
statement or dependency interface is changed, and no new independent notion
is introduced. The auxiliary declarations are the rings and canonical maps
already explicitly defined in this node's statement.

Source read: Stacks `more-algebra.tex`, Tag 09II,
`proposition-epp-essentially-finite-type`, especially the paragraph beginning
“By construction, the field”, and the normalization diagram preceding it.
Read the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md`
and its proof: its current direct-image argument does not state this historical
auxiliary algebra lemma. The item's explicit ten-step transition-system refinement
is followed, including its arbitrary algebraic extension and faithful-flatness
clauses. No correction to the current blueprint or to the node is needed.

Hypotheses, one by one:

- `A : Type u`, `B : Type v`, `[CommRing A]`, `[CommRing B]`, `[IsDomain A]`,
  `[IsDomain B]`, `[IsDiscreteValuationRing A]`, `[IsDiscreteValuationRing B]`
  are exactly the two discrete valuation rings. The class includes locality,
  principal ideals, and the nonzero maximal ideal; fields are excluded as required.
- `[Algebra A B]`, `[IsLocalHom (algebraMap A B)]`, and
  `hinj : Function.Injective (algebraMap A B)` give the injective local map.
- `K : Type w`, `L : Type x`, `[Field K]`, `[Field L]`, `[Algebra A K]`,
  `[Algebra B L]`, `[IsFractionRing A K]`, and `[IsFractionRing B L]` give the
  stated fraction fields. `[Algebra K L]`, `[Algebra A L]`,
  `[IsScalarTower A K L]`, and `[IsScalarTower A B L]` record that K -> L is
  the extension induced by A -> B. These are coherent structure data for the
  same commutative diagram, not an extra restriction on the local map.
- `P : Type y`, `[Field P]`, `[Algebra K P]`, `[Algebra.IsAlgebraic K P]`
  give the arbitrary algebraic extension. `[Algebra A P]` and
  `[IsScalarTower A K P]` only record its induced A-algebra structure.
  The five universe levels are independent and explicitly bound. The index
  is a subtype of `IntermediateField K P`, hence in the universe of P.

Definitions and conclusions, clause by clause (all names below are in namespace
`Algebra.NormalizationTransition`):

- I is `finiteStages (K := K) P`, the subtype of intermediate fields F with
  `FiniteDimensional K F`, with the inherited inclusion order. The first two
  conjuncts are `Nonempty I` and `∀ F G, ∃ H, F ≤ H ∧ G ≤ H`. No nonemptiness
  or directedness is assumed as a hypothesis.
- E_Q is `reducedTensor K L Q`, literally `(L ⊗[K] Q) ⧸ nilradical (L ⊗[K] Q)`.
  R_Q is Mathlib's `integralClosure A Q`; C_Q is
  `integralClosure B (reducedTensor K L Q)`; T_Q is
  `B ⊗[A] integralClosure A Q`. P itself, rather than a replacement field
  or an unspecified ring, is used at the apex.
- `reducedMap` is the tensor map `id_L ⊗ f`, passed to the quotient by the
  nilradical. Its well-definedness uses the existing theorem that a ring map
  sends nilpotents to nilpotents. `closureMap` is `AlgHom.mapIntegralClosure`
  applied to the inclusion with scalars restricted to A. `secondClosureMap`
  applies the same existing restriction to the reduced tensor map over B.
  `tensorMap` is `id_B ⊗ closureMap`. Thus all maps are the prescribed maps.
- `firstTransition`, `secondTransition`, `tensorTransition` specialize these
  formulas to `IntermediateField.inclusion h`; `firstToApex`, `secondToApex`,
  `tensorToApex` use the actual inclusion `F.1.val : F.1 →ₐ[K] P`.
  The third conjunct asserts injectivity of E, R and C transitions between
  finite stages; the fourth asserts injectivity of their maps into the apex.
  No injectivity is added for T transitions.
- `firstDiagram`, `secondDiagram`, `tensorDiagram` are actual
  `I ⥤ CommRingCat` diagrams on exactly R_F, C_F and T_F. Their maps are
  the preceding ring homomorphisms. Their three corresponding `Cocone`
  definitions have apex exactly R_P, C_P and T_P, with those fixed inclusion
  legs. The auxiliary named theorems `firstLaws`, `secondLaws`, `tensorLaws`
  state identity, composition, and compatibility with the apex; their
  complete proofs are described in their docstrings and are postponed.
  Only the proof fields of the actual diagrams and cocones depend on them.
- The next three conjuncts are
  `Nonempty (IsColimit (firstCocone ...))`, and likewise for the second and
  tensor cocones. Mathlib's `IsColimit` is the recorded categorical universal
  property, including existence and uniqueness of descents for every ring
  cocone. This is exactly the assertion that the three displayed canonical
  maps from chosen colimits to R_P, C_P and T_P are isomorphisms: uniqueness
  of colimits gives the comparison with its specified legs. The chosen
  colimit's existence follows from these same witnesses, so no `HasColimit`
  or filtered-category hypothesis has been added.
- `(firstToApex A P F).FaithfullyFlat` for every F gives exactly faithful
  flatness of R_F -> R_P. It uses the recorded ring-map predicate, rather
  than flatness alone or an arbitrarily selected module structure.
- The uniformizer clause quantifies over `a : A`, `b : B` with
  `IsLocalRing.maximalIdeal A = Ideal.span {a}` and the analogous equality
  for B. These equalities are the node's definition of uniformizer.
  `IsLocalization.Away (algebraMap A (integralClosure A F.1) a) F.1`
  says that the *given inclusion* of R_F into F makes F its localization
  away from a; it gives the canonical isomorphism R_F[1/a] = F, including
  compatibility with that inclusion.
- `multiplicationMap A B Q` is the tensor product's `productMap` of the
  canonical map from B into E_Q and R_Q -> Q -> E_Q. It sends b ⊗ r to
  the class of the tensor of the image of b in L with r in Q.
  The same uniformizer clause supplies a ring map from
  `Localization.Away (algebraMap B (B ⊗[A] integralClosure A F.1) b)` to
  E_F, with its composite with the localization's algebraMap *equal to*
  `multiplicationMap ... F.1`, and asserts `Function.Surjective m`.
  The localization universal property uniquely determines m by this
  equality; it is not an arbitrary surjection between these rings.
- `multiplication_mem_closure` states the well-definedness of the node's
  multiplication map into C_Q, with a natural-language proof of the
  monic-equation/subring argument. `multiplicationToClosure` is the actual
  `AlgHom.codRestrict` of `multiplicationMap` using that proof. Its data
  is unchanged multiplication, not an existence choice. The last two
  conjuncts say its underlying ring map is `RingHom.IsIntegral`, for
  every finite stage and for P. This means each element of C_Q satisfies
  a monic polynomial over T_Q via precisely this map.
- There is no hypothesis asserting Noetherianity of R_P, finiteness of
  C_P over T_P, essential finite type of B over A, or separability of any
  field extension. The main theorem docstring carries all ten steps of
  the DAG proof, with their dependency identifiers.

Dependency declarations used, with their full signatures/docstrings inspected:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing` (58), `irreducible_iff_uniformizer` (93);
  proof plan `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` (338).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (95).
- `Mathlib.RingTheory.Algebraic.Defs`: `IsAlgebraic` (45) and
  `Algebra.IsAlgebraic` (68).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` (216);
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: `IsIntegral` and
  `RingHom.IsIntegral`; `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`:
  `AlgHom.mapIntegralClosure` (172), used instead of copying integral closure.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` (81);
  `Mathlib.RingTheory.TensorProduct.Basic`: its commutative ring and algebra
  structures, `Algebra.TensorProduct.includeRight`, `includeLeft`, `ext`;
  `Mathlib.RingTheory.TensorProduct.Maps`: `map` and `productMap` (810).
- `Mathlib.CategoryTheory.Limits.HasLimits`: the recorded categorical
  colimit interface; `Cocone`, `IsColimit` (the latter's fields read in
  `Limits/IsLimit.lean:62`), with no duplicate colimit predicate.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat` (25),
  the ring-map declaration explicitly included in the dependency record.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic`: `IsLocalization.Away` (50),
  and its canonical lift characterization (147-159).
- Proof imports: `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`
  (`IntermediateField.finiteDimensional_adjoin`, 590),
  `Mathlib.RingTheory.Flat.Basic` (`Algebra.TensorProduct.includeLeft_injective`, 410),
  `WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
  (`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`,
  complete recorded theorem and proof docstring read),
  `Mathlib.RingTheory.Flat.TorsionFree` (the Dedekind torsion-free flatness instance, 143),
  `Mathlib.RingTheory.Spectrum.Prime.Topology`
  (`RingHom.IsIntegral.comap_surjective`, 1226), and
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
  (`Module.FaithfullyFlat.of_comap_surjective`, 48).
  Modules also needed to construct the statement are public imports;
  modules used only by its proof are plain imports.

Edge cases checked before writing and again against the final signature:

- P=K: the bottom intermediate field is a finite stage, all three cocones
  have the expected identity-stage model, and faithful flatness includes
  the identity map. No positive-degree extension is required.
- B=A and the identity local map: both fraction fields can be the same;
  the tensor and multiplication constructions remain defined and correct.
- Infinite algebraic P/K: the index remains a small subtype of the set P;
  no finite-dimensional, Noetherian, or finite-spectrum hypothesis is
  imposed at the apex.
- Purely inseparable F/K: for example K=F_p(s), L=F=F_p(s^(1/p)), the raw
  tensor has nilpotents. The quotient by its nilradical is retained, and
  no separability or raw-tensor reducedness assumption occurs.
- Ramified local maps with a=u b^e, e>1: localization inverts b, not just a;
  surjectivity is stated for the canonical multiplication extension and
  does not mistakenly assert it is injective.
- Uniformizers are nonzero and nonunits because the DVR maximal ideal
  is nonzero and proper. Neither a=0 nor a unit can satisfy the displayed
  equality. Zero rings and fields are excluded by the *given* DVR notion.
- Independently sized A, B, K, L, P: all five universe variables are
  declared, no universe equality is imposed, and the colimit category
  has the correct respective ring universes. No quantification over
  test objects in a smaller unrelated universe occurs.

Searches actually run:

- `msearch.py ... leanfinder`: “Integral closures in finite intermediate
  fields form an injective directed system whose colimit is the normalization
  in an algebraic extension”. Eight hits, mainly normal-closure instances,
  `Field.Emb.Cardinal.directed_filtration`, and
  `integralClosure.isFractionRing_of_finite_extension`. None states this
  transition system or its clauses together.
- `msearch.py ... loogle 'integralClosure, "colimit"'`: zero hits.
- `msearch.py ... grep
  'integralClosure.*colimit|colimit.*integralClosure|def.*(map|lift|inclusion)'
  RingTheory/IntegralClosure`: 16 hits, including the usable
  `AlgHom.mapIntegralClosure`; no matching whole statement.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for normalization/transition
  combinations and the exact item identifier: unrelated sheaf and derived
  normalization results, no algebraic normalization transition system.
  Further name searches of those trees and Mathlib found no duplicate
  `Algebra.NormalizationTransition` namespace or new declaration names.
- Read the matching tensor, quotient, intermediate-field inclusion and
  localization declarations in Mathlib. These provide the constructions
  used in this module; no private replacement of any dependency is made.

No statement dispute or node fault was found. The retired example
`Sheaf/CategoryTheory/CompactObject.lean` was read: it currently has only
its withdrawal marker. The delivery uses the module-mode header and
`@[expose] public section` required by the current standing brief.

## Second reading by Q80

This is a second pass by the same dispatched worker; the assignment prohibits
starting another agent. The maintainer performs the independent delivery review.

I reopened the node and the final module and matched every hypothesis and every
conjunct as above. In particular, I checked that all three cocones have the actual
R_P/C_P/T_P apex, that their legs are the explicit inclusions rather than an
existential cocone, that no injectivity of the T diagram was asserted, and that
faithful flatness uses the R_F -> R_P inclusion. I checked that the localization
map is fixed by its composite with the localization inclusion and that the
integrality predicate refers to `multiplicationToClosure`, not a new map.
I checked P=K, infinite algebraic P and inseparable raw tensors against the
binders. The separate A/B and A/K scalar-tower instances express the same
fraction-field square and do not identify the five universes. The first compile
of the packaged diagrams exposed undetermined implicit K/L parameters; these
were made explicit at the affected calls. The complete statement then compiled;
a single 109-character line was wrapped to satisfy the 100-character rule.
No mathematical mismatch or statement correction was needed.
