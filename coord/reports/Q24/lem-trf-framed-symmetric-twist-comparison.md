## Worker report

The module `Sheaf.AlgebraicGeometry.FramedSymmetricTwistComparison` states
`AlgebraicGeometry.exists_framedSymmetricTwistComparison`, with `sorry` as its only
postponed proof. No theorem is proved. The original statement is unchanged.

The main conclusion bundles the sectionwise isomorphisms and their equations in
`FramedSymmetricTwistComparison E L`. This structure is the conjunction of this node's
conclusions, not an assumption about the input. Its `tau` and `beta` fields are on every
subopen of every framed open. A natural family of linear equivalences is precisely an
isomorphism of the restricted module sheaves; a natural family of ring equivalences
commuting with structural scalars is precisely an isomorphism of the restricted algebra
sheaves. This avoids adding a choice of restriction comparison as a hypothesis.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A scheme S | `(S : Scheme.{u})`, with explicit universe `u` |
| A finite type quasi-coherent E | `(E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteType]` |
| An invertible L | `(L : S.Modules) [L.IsInvertible]`, the recorded scheme predicate |
| Every natural n, with L tensor-power zero = O | `n : ℕ` in the conclusion; the existing `L.tensorPow n`, whose zeroth value is the monoidal unit |
| E_n = E tensor L tensor-power n | The actual tensor object `E ⊗ L.tensorPow n` throughout |
| E_n is quasi-coherent and finite type | `∀ n, (E ⊗ L.tensorPow n).IsQuasiCoherentFiniteType`, the recorded conjunction |
| Sym(E), Sym(E_n), canonical j | `SymmetricAlgebraSheaf.algebra` and `SymmetricAlgebraSheaf.inclusion`; these are the explicit canonical model used by the symmetric-algebra dependency |
| Every open U and frame e | `U : S.Opens`, `e : Γ(L,U)`, and `Scheme.Modules.IsFreeGenerator e`, meaning multiplication by e gives a sheaf isomorphism on U, on all its subopens |
| The module isomorphism tau | The `tau` family of `≃ₗ[Γ(S,V)]` on every `V ≤ U` |
| tau(v) = v tensor e tensor-power n | `tau_apply`, using `tmulSection` and `framedTensorPowerSection` applied to the restriction of e |
| Inverse v tensor a e tensor-power n maps to a v | `tau_inverse`; equivalences supply both inverse identities |
| Unique graded algebra isomorphism beta | `beta`, `beta_scalar`, `beta_generator`, `beta_graded`, and `beta_unique`; the competitor in uniqueness is a graded natural family of ring equivalences fixing scalars and the prescribed generators |
| Its inverse extends tau inverse | `beta_inverse_generator` |
| Affine-section normalization | `beta_affine` and `beta_inverse_affine` compare the maps through the existing canonical `sectionMap`, which is an isomorphism on affines by the recorded quasi-coherent symmetric-algebra theorem |
| Maps in both directions commute with every smaller-open restriction | `tau_natural`, `tau_inverse_natural`, `beta_natural`, `beta_inverse_natural`; these quantify over arbitrary opens and inclusions |
| beta restricted to V is beta for the restricted frame | `beta_restrict`; `he.map h` is the existing restriction theorem for frames |
| A unit u and e' = ue | `c : Γ(S,U)ˣ`, with the new frame written directly as `(c : Γ(S,U)) • e`; `he.units_smul c` supplies its frame proof, with no additional hypothesis |
| tau change is u^n tau | `tau_change_frame`, including the restriction of c to each V |
| For all k ≥ 0 and local homogeneous sections, beta change is u^(nk) beta | `beta_change_frame` with `k : ℕ` and `IsLocallySymmetricHomogeneous E k V a`; scalar action is multiplication by the image of the restricted unit power under the structural ring homomorphism |
| n = 0 gives the canonical unit identifications | `tau_zero` identifies tau with the inverse right unitor. `beta_zero_generator`, together with scalar normalization, grading, naturality and `beta_unique`, identifies beta with its unique symmetric extension. `beta_zero_independent` records frame independence |

The two elementary helpers contain real definitions. `framedTensorPowerSection` recursively
uses the existing `unitSectionsEquiv` and `tmulSection`, matching the existing recursion for
`tensorPow`; the existing `tensorPowSection`/`tensorPowSectionOne` instead take a global
module morphism, and cannot accept an arbitrary local section on the ambient scheme.
`IsLocallySymmetricHomogeneous` expresses membership in the symmetric-degree subsheaf by
local affine sections in `(SymmetricAlgebra.ι ...).range ^ k`. It uses the existing canonical
affine-basis grading. In particular it does not erroneously require a homogeneous section
on a nonaffine open to be in the image of the degree-k presheaf on that entire open.
These helpers and the aggregate conclusion are specific interfaces for this statement,
not replacement definitions of tensor products, symmetric algebras, frames or grading.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, definitionally
  `SheafOfModules.IsQuasicoherent ∧ SheafOfModules.IsFiniteType`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, `tensorPow`, and the canonical monoidal structure.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded general-site tensor interface, based on the existing localization tensor.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `exists_quasiCoherentSymmetricAlgebra`, including the sheaf universal property and the
  scalar/generator-normalized affine isomorphism.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, including the monomial-span description.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `SymmetricAlgebraSheaf.algebra`, `inclusion`, `sections`, and `sectionMap`.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `sectionGradedAlgebra`, `gradedRestriction`, and `gradedAlgebraData`; the grade is
  precisely the nth power of the degree-one range.
- `WeilConjectures.AlgebraicGeometry.Modules.TensorSection` and its public frame import:
  `tmulSection`, `unitSectionsEquiv`, `IsFreeGenerator`, `IsFreeGenerator.map`, and
  `IsFreeGenerator.units_smul`.

The canonical construction and canonical grading nodes are already landed and were already
proof dependencies. They are also added to `stmt_deps`, since their canonical model now
occurs in the statement. No dependency record is repaired and no new node is needed.
All already recorded proof-dependency modules are imported, including the sheafification
restriction and symmetric universal-property core modules. The declaration docstring gives
all seven steps of the node proof, with their dependency ids.

Source read: `literature/stacks-project/constructions.tex`,
`lemma-twisting-and-proj` (Tag 02NC), including its proof: trivialize on an open cover
and glue. This item supplies the local symmetric-algebra calculation for that proof;
it does not change the blueprint unit or the relative-Proj statement.

Edge cases checked before and during writing:

- Empty S and empty U: no nonemptiness or affine restriction is imposed; the local grade
  condition is vacuous on an empty open, as required for its unique section.
- E = 0: no rank, freeness, finite-presentation or nonzero assumption on E is used.
- n = 0: recursion returns the structural unit; tau is the inverse right unitor;
  beta is the uniquely normalized symmetric extension and is frame independent.
- k = 0: the grading is the scalar component and the transition exponent is zero.
- n > 0 and arbitrary characteristic: the exponent n*k needs no inverse of an integer.
- Nonaffine subopens and nonfree finite-type E: every restriction law is on arbitrary
  opens, and homogeneous membership is local on the affine basis.
- Non-Noetherian S and nontrivial L: no global frame or global freeness hypothesis appears;
  the comparison system ranges over every local frame where one is given.

Searches actually run (all on 2026-10-24):

- `msearch.py leanfinder`: “Symmetric algebra sheaf comparison induced by a frame of an
  invertible module, preserves grading and scales degree k by u to power n k”. Eight hits,
  mostly free-sheaf formulas and `IsSymmetricAlgebra.comp_equiv`; none is this comparison.
- `msearch.py loogle`: `SymmetricAlgebra.map, SymmetricAlgebra.lift, SheafOfModules.tensorObj`.
  Zero hits, with diagnostic `unknown identifier 'SymmetricAlgebra.map'`; this is not
  recorded as a successful search for that identifier.
- `msearch.py grep` in `LinearAlgebra/SymmetricAlgebra`:
  `symmetric.*twist|framed.*symmetric|SymmetricAlgebra.lift`. Seven hits concerning the
  ring-level universal property and basis; none states the framed sheaf comparison.
- `msearch.py leansearch`: “symmetric algebra sheaf isomorphism under tensoring with a
  trivialized invertible sheaf, degree scaling by a unit”. Eight hits including
  `IsSymmetricAlgebra.of_equiv` and tensor unit formulas; none states the item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the framed/symmetric twist terms found
  `RelativeProjInvertibleTwist` (the parent Proj theorem), the canonical symmetric algebra,
  `TensorSection` and global `tensorPowSection`, but no declaration with this full statement.
- `grep -rn` for the item id in `lean/WeilConjectures` found none. Searches for the four new
  declaration names in Mathlib, both source trees and `dag/lean_names_upstream.json` found
  no collision. The upstream global tensor-power section interface was opened and read.

Validation: the module compiled in module mode using `scompile.py`, in both sandbox and
library passes, with no warnings or errors. `deliver2.py --no-push` returned OK: commit
`fd27e46f2c3` passed server preflight and compilation. The packet is delivered with the
prescribed `deliver2.py` wrapper. No `STATEMENT-DISPUTED` flag or statement correction
is needed.

## Second reading by Q24

A second pass by this worker checked the node against the structure fields and the main
signature. It changed uniqueness from all algebra maps to graded algebra isomorphisms,
matching the node literally, and replaced a supplied proof that ue is a frame by the
existing `IsFreeGenerator.units_smul` proof. It also checked the inverse affine formula,
all four naturality laws, arbitrary-open homogeneous sections, and n = k = 0. There is no
independent worker second reading: under this assignment the maintainer performs the
independent review after direct delivery.
