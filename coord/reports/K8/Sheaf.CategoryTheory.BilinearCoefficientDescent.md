## What changed

Prove all raw tensor, common-stage, rational-system and p-adic coefficient-descent
clauses. The raw arrow map is the bilinear tensor base change of the integral map.
The common-stage argument uses the fully faithful diagonal from the product stage
system and the existing StageSystem representative/transport/equality API. The
finite coefficient theorem combines these constructions with the recorded
uniformizer localization and finite compositum results. All 20 original theorem
signatures are unchanged.

Repair the data definitions to avoid repeated large reductions. Units uses an
equivalent subtype. Family and Transformation use structures with compact internal
fields; wrappers retain their named projections, constructors and laws. UnitLaws,
FamilyTower and TransformationSquare name the unchanged proof constraints.
Five specification predicates are proposition structures; proved iff lemmas identify
them with their original clauses. The private bilinear linear map is stored as
rawHomLinear and evaluated by the ordinary function rawHom. Its six proved
bilinearity equations and pure-tensor formula keep later proofs from repeatedly
synthesizing coercions and general homomorphism classes. The private tensorComp
interface similarly evaluates the existing scalar-localized composition map, with
proved zero, addition and pure-tensor laws. All private simp rules are local. The integral and common-stage
pairing constructions stay folded after their APIs are proved. A local priority for
Mathlib's existing vector-space torsion-free instance speeds coefficient-field
searches without adding a Hom torsion hypothesis.
The private diagonal and explicit common-stage functor have direct object fields
and retain the same composite maps. The public raw and descended functors use
`withObjects` to have their stipulated object fields directly; `withObjects_eq`
proves equality with the original uniquely chosen functor. Their complete
prescriptions and component formulas are public proved lemmas. Both
respectTransparency options remain true; no debugging options are delivered.

Use explicit canonical subring ring/algebra instances. The coefficient
uniformizer/inclusion have folded exported bodies (`no_expose`).
`uniformizer_val` and `integerInclusion_apply` prove their exact field actions. Hide the integer-ring alias
behind `Integers_eq`, and construct the uniformizer with exactly the same recorded
field value and a separate proved membership lemma. Construct integerInclusion
directly from the actual field inclusion; its membership proof uses spectral-norm
uniqueness and the DVR membership formula. The localization conversion explicitly
identifies the subrings, elements and implicit instances. No arbitrary object is
chosen from an undetermining existence statement and no Hom torsion hypothesis is
added. The definition repairs and consumer compatibility are documented in
`coord/changes/K8-bilinear-coefficient-canonical-instances.md`.

Repair the returned import-pruning failure by retaining the original public imports
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`Sheaf.Paper.IntegralScalarExtensionWellDefined`, and
`WeilConjectures.CategoryTheory.StageSystem.Preadditive`. This preserves the
consumer's public declaration environment. No consumer file is changed.

## Proved and sorry left

Closed all 20 original holes, with no holes added and no split-off statements.
All declaration names are in `CategoryTheory.BilinearCoefficientDescent`:

- `raw_extension_existsUnique`
- `raw_comparison`
- `raw_transformation_existsUnique`
- `raw_equations`
- `raw_whisker_output`
- `raw_whisker_input`
- `raw_additive`
- `descent_existsUnique`
- `transformation_existsUnique`
- `descent_equations`
- `change_common_field`
- `finite_equation_descent`
- `whisker_output`
- `whisker_input_left`
- `whisker_input_right`
- `rational_system_existsUnique`
- `rational_comparison`
- `coefficient_hypotheses`
- `compositum_upper`
- `bilinear_comparison_coefficient_descent`

No `sorry` remains in the item module. No new statement or hole is introduced.
The two-file artifact check passed: the item artifact build completed in 46.6
seconds, and the unchanged sole consumer compiled against it. The unused simp
arguments reported in that run are removed. The required delivery performs its
independent compile and axiom checks.
No source-library declaration is modified and no target signature is changed.

## No longer needed

- Direct import `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the abstract StageSystem
  quotient category supplies the common-stage model; no geometric coefficient
  category or constructible-object hypothesis is used.
- Direct import `Sheaf.CategoryTheory.LinearScalarLocalization`: redundant through
  ScalarLocalization. Its node `lem-weil-linear-scalar-localization-category` is
  still needed transitively by the actual composition construction and remains a
  proof dependency.
- `Mathlib.Algebra.Colimit.Module` and proof dependency
  `def-weil-directed-colimit-abelian-groups`: the adopted StageSystem calculus
  already supplies representatives, transport, composition and eventual equality.
The geometric scalar-extension construction, pair-category preadditivity and
finite integer-ring quotient assertions are not used in this proof. Their three
original public imports are retained to preserve the downstream public environment,
as requested by the return; these modules are not claimed as pruned.

Retain Mathlib.LinearAlgebra.TensorProduct.Tower for
AlgebraTensorModule.distribBaseChange and LinearMap.baseChange. No adopted source
module or declaration is withdrawn. No additional DAG node is required by the
proved constructor and normalization API, which belongs to the existing owning node.

## Where the brief, the DAG or earlier work was wrong

The retained proof exceeded the compile limit. Its large data reductions are
replaced by folded representations, characterizing lemmas and explicit object
fields. The old cached instance searches are replaced by the canonical constructors.

The planned abelian-group direct limit is unnecessary: the existing StageSystem
quotient calculus supplies the shorter construction. The input-whiskering
isomorphisms still include the beta comparison in their specified slot, with the
stated representative at every upper stage. Importing the coefficient restriction
through the geometric scalar-extension theory, and importing finite quotient
results and pair-category preadditivity, were unnecessary dependencies.


The import-pruning return identified declarations used through the original public
imports. Those imports are restored. No downstream adaptation remains in the packet.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
