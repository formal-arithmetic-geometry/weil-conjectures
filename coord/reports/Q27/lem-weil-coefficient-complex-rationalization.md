## Worker report

The module `Sheaf.Paper.CoefficientComplexRationalization` states the whole node using
several named theorems in its `lean.declarations`. Every theorem has proof `sorry` and
a natural-language proof plan; all definitions have real data. No statement correction or dependency module is required. The added statement
dependencies are the landed fixed-closure indexing type and the landed Q134 node
`def-weil-pbc-integer-quotient-inclusions`, which already owns the existing restriction
of a field inclusion to the specified valuation subrings. This delivery adds no node.

Hypotheses and clauses, checked against the node and the final source paragraph:

- Prime ell: `(l : ℕ) [Fact l.Prime]` in all coefficient declarations.
- Fixed algebraic closure: `(Q : Type u) [Field Q] [Algebra (Padic l) Q]
  [IsAlgClosure (Padic l) Q]` in `coefficientComplexRationalization`.
- Finite subfields and inclusions: `(E L M : Padic.FiniteCoefficientFields l Q)`
  and `(hEL : E ≤ L) (hLM : L ≤ M)`. The indexing type is exactly the subtype of
  intermediate fields with `FiniteDimensional (Padic l) E.val`; its existing
  instance supplies this property. The maps are `IntermediateField.inclusion`;
  the composite is the composite of these very inclusions. The helper declarations
  accept finite coefficient fields and an algebra embedding; any such finite tower
  embeds in an algebraic closure, so this form introduces no additional case or
  hypothesis beyond the finite-subfield formulation.
- Integer rings: the actual `Padic.coefficientExtensionIntegers l E`, not a fresh
  unit-ball subring. `integralScalarIntegerInclusion` owned by the landed definition node
  `def-weil-pbc-integer-quotient-inclusions` is the restriction of the field inclusion. The latter's
  source and docstring were read in full through its membership proof.
- Arbitrary unbounded N: `CochainComplex (ModuleCat.{max u v} O_E) ℤ`, with no
  boundedness, finite-generation, torsion-freeness, completeness or perfectness
  assumption on N. Both universes are explicit, so all module sizes at least the
  ring size are available. A common universe is harmless for the three subfields
  of the fixed closure.
- All tensors are ordinary: the three public tensor aliases expand directly to
  `ModuleCat.extendScalars`, and the cochain functors are `mapHomologicalComplex
  (ComplexShape.up ℤ)`. Mathlib uses `B ⊗_A N`, rather than `N ⊗_A B`; this is
  precisely the tensor-order convention already authorized by the base-change
  node's recorded interface, via tensor commutativity.
- Existence and module naturality: `coefficientComplexBeta_existsUnique` specifies
  a natural L-module isomorphism of the two module composite functors by its full
  generator formula. `coefficientComplexBeta` selects its unique witness, which
  is determined up to equality, not an arbitrary witness of bare existence.
- Chain comparison: `coefficientComplexChainBeta` is the degreewise
  `NatIso.mapHomologicalComplex` of that natural isomorphism. In
  `coefficientComplexComparison_spec`, the first conjunct gives the formula
  `b ⊗ (a ⊗ n) ↦ (b * a) ⊗ (1 ⊗ n)` in every degree. The second conjunct says
  every natural chain isomorphism with that formula equals this one. Together
  these give existence and uniqueness exactly as stated. Chain morphisms are
  morphisms in a category of modules, so each component is automatically L-linear.
- The inverse formula is the third conjunct of `coefficientComplexComparison_spec`:
  `b ⊗ (x ⊗ n) ↦ (b * ι x) ⊗ (1 ⊗ n)`, for every `x : E` and `b : L`.
  These are actual field elements, with no integrality restriction. In particular
  they include every fraction in E or L. Since expressions for fractions already
  denote equal elements of those fields, both displayed maps are functions on
  those elements and hence independent of their fraction presentations. No
  presentation or denominator choice is part of the construction, and no division
  of n is used. There is no extra fraction-independence axiom or hypothesis.
- Four additive exact functors: `coefficientComplexTensors_exact` contains, for
  Q_(L/E), q_E, q_L, and V_(L/E), their `Additive`, `PreservesFiniteLimits`, and
  `PreservesFiniteColimits` structures. The nine named instance definitions merely
  project the uniquely determined structures from these propositions.
- Preservation of quasi-isomorphisms: the next four conjuncts of
  `coefficientComplexComparison_spec` are the existing
  `HomologicalComplex.preservesQuasiIso` predicate for the four termwise functors.
- Derived categories are localization: `coefficientComplexModuleDerived` uses
  `HasDerivedCategory.standard` on the actual module category; the four derived
  functors are Mathlib's `Functor.mapDerivedCategory` with its localization
  factorization `mapDerivedCategoryFactors`. The component morphism universe
  comes from that standard localization, with no equality imposed on unrelated
  site universes (there is no site here).
- Derived comparison and arbitrary derived naturality:
  `coefficientComplexDerivedBeta` is constructed using
  `Functor.mapDerivedCategoryNatIso` between the exact composite module functors,
  conjugated by `mapDerivedCategoryCompIso`. This is a natural isomorphism on the
  full derived categories, including all their arrows, rather than a family of
  arrows only on chain representatives. The final conjunct of
  `coefficientComplexComparison_spec` identifies its component on Q(N) with the
  localized chain beta through the specified composite factorization isomorphisms
  `coefficientComplexDerivedFactors`. This prevents an unrelated derived map.
- Identity E=L: conjuncts one and three of `coefficientComplexRationalization`
  assert equality to the identity under the integral and field multiplication
  identifications, for every N and every derived K. Those identifications are
  `coefficientComplexIntegralUnit` and `coefficientComplexFieldUnit`, with their
  chain and derived versions. They use Mathlib's `extendScalarsId` after the
  separately named integer-identity equality.
- Tower E⊂L⊂M: conjuncts two and four of
  `coefficientComplexRationalization` are exactly the node's two paths, on all
  complexes N and all objects K of D(O_E). Left: apply q_M to the integral
  associator and then beta_(M/E). Right: beta_(M/L) at Q_(L/E)N, then V_(M/L)
  of beta_(L/E), then the field associator. These are equalities of chain maps
  and derived maps, respectively. The integral associator is Mathlib's
  `extendScalarsComp.symm`, transported along the equality of the actual
  composite integer maps; the field associator is the same Mathlib associator.
  Their multiplication formulas include arbitrary field coefficients. The
  associator maps, beta maps and whiskerings are natural, so the equalities at
  every K are also equalities of the corresponding natural transformations.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` /
  `Padic.finite_coefficientExtensionRing`, importing `CoefficientExtension` /
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionAbsoluteValue`,
  and the other recorded coefficient constructions. The integer subring is the
  DVR witness characterized by its absolute-value membership condition.
- `Mathlib.LinearAlgebra.TensorProduct.Tower` / `LinearMap.baseChange`,
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.AlgebraTensorModule.distribBaseChange`.
  `ModuleCat.extendScalars` applies precisely this `baseChange` on maps; the full
  implementation and its coefficient-first tensor convention were inspected.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` / `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- Added landed dependency `def-weil-finite-subextension-directed-set`:
  `Sheaf.NumberTheory.Padics.FiniteCoefficientFields` / `Padic.FiniteCoefficientFields`,
  `Padic.finiteCoefficientField_finiteDimensional`.
- Landed Q134 definition dependency `def-weil-pbc-integer-quotient-inclusions`:
  `Sheaf.Paper.IntegralScalarExtensionWellDefined` /
  `WeilConjectures.integralScalarIntegerInclusion`,
  `WeilConjectures.integralScalar_integer_mem`. The restriction and its membership
  proof are already concretely defined/proved. This item does not use
  `integralScalar_absoluteValue` directly, nor does it acquire ownership of it.
  The completed scalar-extension theorem itself is not a statement dependency.
- Proof leaves are imported: `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`,
  `ValuationRing.iff_isInteger_or_isInteger`, `Module.Flat.lTensor_exact` and
  `rTensor_exact`, `TensorProduct.lift` and `ext'`,
  `Functor.mapDerivedCategoryFactors`, `Localization.lift`, `liftNatIso`,
  `natTrans_ext`, and the module-category Grothendieck-abelian instance.
  Their signatures, implementations and source docstrings were inspected.

Edge cases checked before and after drafting: N=0; torsion modules such as O_E/(s)
(rationalization may annihilate them, but no inverse divides a module element);
complexes unbounded in both directions; arbitrary positive or negative degrees;
E=L, L=M and E=L=M (the actual identity inclusion is used); coefficients x=0,
x=1, and nonintegral fractions; different nonzero-denominator presentations;
and independent larger module universes. The exactness argument is tensor-flatness,
not a finite-dimensional-vector-space argument applied to integral modules.
No statement is disputed and no hypothesis has been added to repair one.

Searches for existing statements (all through prescribed msearch.py and read-only rg):

- LeanFinder: "Rationalization and coherent scalar extension of unbounded complexes
  over rings of integers of finite padic extensions". Eight hits were unrelated
  PadicComplex/BDeRham constructions and scalar tower instances; no whole comparison.
- LeanSearch: "Exact scalar extension and rationalization of complexes over valuation
  rings with coherent tensor associators". Eight hits were valuation-integer scalar
  tower/module structures, not this full statement.
- Loogle: "ModuleCat.extendScalarsComp, ModuleCat.extendScalars_assoc". One hit,
  `ModuleCat.extendScalars_assoc`, provides generic scalar associator coherence.
- msearch grep: "extendScalarsComp|preservesFiniteLimits.*extendScalars" in
  Algebra/Category/ModuleCat. Eleven hits: the scalar associator in ChangeOfRings,
  its pseudofunctor, and finite-limit preservation for flat maps in Descent.
  These exact generic constructions are reused; none states the node's combined
  fraction-normalized comparison with unbounded descent and mixed tower law.
- Read-only rg over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id and the new coefficientComplex
  names found no declaration of this node or name collision. Searches for
  rationalization, coefficient integer inclusions, and scalar associators found
  the actual integer inclusion in IntegralScalarExtensionWellDefined (reused).
- The existing `PointSectionsScalarExtension` module contains closely related
  module comparisons only at the fixed module size u+1; its main theorem is about
  point sheaves and constructible completed objects. It is a downstream node whose
  proof depends on this item, so importing it here would close a dependency cycle.
  The present aliases add no construction: all ordinary tensor data and associator
  data come directly from Mathlib. This node gives the standalone coefficient-
  module theorem at arbitrary size, without point geometry or constructibility.

Validation: prescribed scompile.py compiled both the sandbox and library forms of
the complete module without errors or warnings (44.2 s and 46.4 s before adding the
explicit imports of already-transitive dependency modules). The final delivery
preflight recompiles the exact final file. No local build, direct git operation,
shared-repository edit, or launcher-file edit was performed.

## Second reading by Q27

I made a separate pass with the node and final Lean source open; this is a second
pass by the same dispatcher worker, not a claim that another agent reviewed it.
The brief prohibits starting another agent; the maintainer supplies the independent
review. I matched every hypothesis and clause as itemized above. In particular I
rechecked the two tensor-order translations, the inverse formula with nonintegral x,
the uniqueness quantifier over all natural chain isomorphisms, and the component
factorization square fixing the derived comparison. The four final equalities use
the right source and target: both tower routes start with q_M Q_(M/L) Q_(L/E) and
end with V_(M/E) q_E. The derived law quantifies over an arbitrary K, not just Q(N).
The identity laws use the actual identity integer inclusion, with the equality
transport named separately. The two ring-map equalities have no hidden proof in a
definition: they are named theorems with proof plans and `sorry`. The only elaboration
repair was qualifying `Functor.isoWhiskerLeft`; no mathematical statement changed.
All declarations are public, every universe is explicit, and all lines are at most
100 characters. No mismatch or source-based correction was found.


## Repair of return 0ab0d85152f0

The H12/H4 ownership defect is repaired exactly as requested. In the item's
`stmt_deps`, replaced `def-weil-coefficient-integer-inclusion` with the landed
Q134 definition node `def-weil-pbc-integer-quotient-inclusions` (FIX f945b662).
Deleted the redundant new-node JSON from the packet and updated `lean.note` and
this report. No new nodes or dependency modules remain in this delivery.

Read the landed Q134 node's full statement and Lean record and the existing
`IntegralScalarExtensionWellDefined` source through the membership proof and
integer-inclusion definition. Its primary declaration is exactly the map used by
`coefficientComplexIntegralTensor` and all tensor formulas. It also owns
`integralScalar_integer_mem`; the extra proved lemma `integralScalar_absoluteValue`
is not used by this item and needs no new owner here. The quotient constructions
owned by Q134 are not used in this item. The completed scalar-extension theorem
remains absent from the item's statement dependencies.

Compared the saved packet with current main: only the permitted `lean` and
`stmt_deps` fields differ in the item node. The wrapper rebases onto current main.
The Lean module is unchanged from the saved packet independently checked at
0ab0d85152f0 and previously fully reviewed at 818d69d5. The node's statement,
proof, proof dependencies and Lean signatures are unchanged. The initial saved
packet passed the prescribed dry run (commit e230154dc67); that mechanical pass
did not repair the ownership defect, so the correction above was still made.

Second reading of the repair by Q27: the actual restriction sends an integral x
to the same field element iota(x), and `codRestrict` uses the recorded membership
proof. This is the exact inclusion required for arbitrary finite E/L and for
identity and tower inclusions. No hypothesis or clause changes, so all original
clause-by-clause and edge-case checks above remain applicable. This reading is by
the same worker; independent review remains the maintainer's responsibility.

Repair validation: prescribed scompile.py passed both the sandbox form (38.9 s)
and the final library form (57.6 s), with no errors or warnings. Self-check confirmed
only permitted item fields changed, the duplicate node is absent, both additional
statement dependencies are landed, the recorded signature is verbatim, and the
unused absolute-value helper is absent from the module.
