## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.nonempty_smoothPurityIso`
in `Sheaf.Targets.SmoothPurityQbar`. Its sole postponed proof is the existence of
an isomorphism between the exact two ambient derived objects of the target.
`Nonempty (A ≅ B)` states “there is an isomorphism”; it introduces no hollow
isomorphism data and does not choose an arbitrary map. Nothing is proved in this
stage-2 module. The natural node statement, statement dependencies, proof and
proof dependencies are unchanged.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| An arbitrary field of positive characteristic p | `{k : Type u} [Field k] [Fact (ringChar k).Prime]`; a field's positive characteristic is prime |
| p differs from ell | `[Fact (ringChar k ≠ ℓ)]` |
| X and Y are schemes over Spec k, f is over k | `{X Y : Over (Spec (.of k))}` and `(f : X ⟶ Y)` |
| X is separated and of finite type | `[IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| Y is separated and of finite type | The same three explicit binders on `Y.hom` |
| Pure relative dimension d is nonnegative | `(d : ℕ)` |
| f is smooth of pure relative dimension d | Explicit declaration binder `[SmoothOfRelativeDimension d f.left]` |
| The finite-extension-valued condensed Qbar coefficient ring | `Profinite.padicAlgClRingObj ℓ`, in its published universe-u version |
| The bounded constructible coefficient unit on Y | `𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)` |
| The chosen exceptional inverse image | `boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f` |
| The fully faithful inclusion into the ambient derived category | `.obj` on the resulting bounded constructible object |
| The actual condensed Tate endpoint | `tateTwistDerived X.left ℓ d` |
| Shift by twice the relative dimension | `(shiftFunctor _ (2 * d : ℤ)).obj` |
| There exists an isomorphism between those objects | `Nonempty (... ≅ ...)` |
| Common-stage coefficients are used through realization, not definitionally identified | The conclusion uses internal condensed modules exclusively; `pbcQbarCategory` and `pbcTateTwist` are imported for the reconstruction route, with no identification or replacement of the conclusion category |
| Intended normalization from finite purity and reconstruction | The theorem docstring follows the node's eight proof steps, including quotient coherence, the exact chosen adjunction, and the degree-zero unit comparison; the node does not impose a further normalization equation on the existential result |

All variables and the scheme universe are explicit; `set_option autoImplicit false`
is also present. All geometric assumptions are declaration binders, rather than
unused section variables which Lean might omit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension` is the recorded smoothness notion,
  with standard-smooth charts of dimension d. Its `smooth` implication is already
  in Mathlib, so no separate smoothness axiom is needed.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, whose objects are
  weakly etale schemes over the base, and `ProEt.topology`. These are reexported
  by the actual condensed coefficient framework.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek`:
  `CondensedRing.boundedConstructibleUpperShriek`, its compactification variant
  and its composite adjunction. The current source uses Over morphisms and
  synthesizes the proper right adjoint at padicAlgCl coefficients. No adjoint
  existence assumption is added to the theorem.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` is the actual choice used by that functor;
  `isMonoidal_boundedConstructible` supplies the coefficient unit in the full
  subcategory at ell-adic coefficients. The full subcategory's underlying-object
  projection is the inclusion in the conclusion.
- `WeilConjectures.TateTwist.ProEtale`: the exact `tateTwistDerived` and its
  real-data tower, scalar-extension and signed-tensor constructions. This is
  also a lean-only repair of `def-pur-condensed-tate-twists`, described below.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` reexports the recorded
  continuous coefficient and module framework. The actual algebraic-closure
  coefficient ring remains the finite-subextension-valued ring, not all
  continuous functions to Qbar.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `constructibleCocone_isFilteredTwoColimit`, reexported by the coefficient
  framework, is the recorded condensed finite-stage two-colimit statement.
- `Sheaf.Paper.PbcQbarCategory`: `Scheme.pbcQbarCategory`, the literal finite-stage
  pair category with actual coefficient-system assumptions.
- `Sheaf.Paper.PbcCoefficientTwists`: `Scheme.pbcTateTwist`, formed on an integral
  representative at its original finite field. These last two definitions are
  distinct from the condensed coefficient category and are not used to replace it.
- Proof-only import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  supplies the recorded `AlgebraicGeometry.exists_topologicalKrullDim_le`.
  The other proof nodes have no published Lean record in the read DAG and
  therefore contribute no proof import. Their full roles are retained in the
  theorem's natural-language proof docstring.

Edge cases checked before writing: d = 0 is permitted, giving the zero shift and
zeroth actual Tate twist, including identity and etale morphisms. Empty X or Y
is permitted: no nonempty-space hypothesis is introduced. The empty morphism is
smooth of any fixed pure dimension vacuously, with both resulting objects zero.
The field can be F_p(t); no finite-field, algebraic-closure or perfection assumption
is added. ell = 2 and every other prime distinct from p are permitted. ell = p,
ell = 0 and characteristic zero are excluded exactly by the original hypotheses.
The coefficient construction's n = 0 term and all-natural-number tower are
preserved through the upstream construction. The shift uses integer arithmetic
`(2 * d : ℤ)` and thus places the Tate sheaf in degree -2d. The size parameter u
is shared by the field and schemes, and coefficient sheaves use u+1 as in the
recorded framework; no object/morphism universe equality was added.

Searches (2026-10-18):

- msearch LeanFinder: `smooth purity exceptional inverse image unit Tate twist condensed algebraic closure coefficients` returned BDeRham, PreTilt.coeff_def, BDeRhamPlus, fontaineThetaInvertP, WittVector.StandardOneDimIsocrystal, PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable, PerfectionMap.comp_symm_equiv and AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit. None states this theorem.
- msearch Loogle: `AlgebraicGeometry.SmoothOfRelativeDimension, CategoryTheory.Iso` returned zero hits.
- msearch LeanSearch: `smooth purity isomorphism exceptional inverse image Tate twist` returned generic smooth algebra/scheme declarations, no purity theorem.
- msearch grep: `smoothPurityIso|boundedConstructibleUpperShriek|tateTwistDerived` in Mathlib CategoryTheory returned zero hits.
- rg in the slopmaster2 WeilConjectures tree for `smoothPurityIso|nt-target-smooth-purity-qbar` found the etale-category smoothPurityIso, whose input is a general complex with finite etale coefficients and whose output is not this condensed target. The target id was absent.
- rg in side `lean/Sheaf` for the target name and id found no theorem. Searches for `nonempty_smoothPurityIso` in the side tree, slopmaster2 and upstream-name index found no declaration.
- Published source inspection with `scompile.py --source` found the exact-named upstream `WeilConjectures.SmoothPurity.Defs.smoothPurityIso` and `Sheaf.SmoothPurity.NormalizedWitness.exists_normalizedSmoothPurityMaps`. Neither is a match: their elaborated types omit smoothness; the latter even explicitly uses `omit [SmoothOfRelativeDimension d f.left]`. They assert the conclusion for arbitrary f and d, which is false for the identity of Spec(F_p) at d = 1, p different from ell. The existing upstream file documents this defect. The present natural node already states smoothness correctly, so no statement_change is needed. This delivery does not import either defective declaration and binds smoothness explicitly.
- Published source inspection also found the usable full Tate construction, chosen compactification, Over factorization and bounded constructible category. Those existing definitions are reused, not restated.

The node is not disputed: its intended smooth statement agrees with the archived
source prose and the current blueprint. The upstream elaboration defect is recorded
above as a reason not to bind the node to the existing stronger declaration.
The route cites only the current blueprint and the permitted coefficient literature;
it uses diagonal/DNC finite purity, coherent towers and the actual chosen adjunction.
No prohibited trace-route source is used.

## Dependency modules

`sk-def-sfb-dc-setting`: the node had no lean record. The existing published
`CondensedRing.compactificationOverField` and `ProEtale.BoundedConstructible`
provide exactly the two objects of the node. The new existing-record declaration
list includes `HasCompactification.of_over` and the Over factorization
`Compactification.overObj`, `overI`, `overG`, `overI_overG`. The documented instances
make the middle scheme separated and finite type over the same base, with no
extra assumption. The setting assumptions are explicit in the target signature.
This supplies the missing genuine prerequisite in this delivery without adding
a duplicate setting definition or module.

`def-pur-condensed-tate-twists`: the recorded side module duplicates names now
provided by the published upstream `WeilConjectures.TateTwist.ProEtale`. The
human's duplicate-declaration repair rule says to prefer that upstream module.
Its source was read in full through `scompile.py --source`: it has exactly the
free-module roots-of-unity levels, power transitions, all-natural-number limit,
inclusion through the bottom finite extension, balanced scalar extension,
nonnegative tensor powers, negative internal Homs and degree-zero localization
of the node. Its existing record replaces only lean. No construction or natural
statement changes; no extra module is written.

## Second reading by N6

No second worker reading: the dispatcher's direct-delivery instruction assigns
independent review to the maintainer. No independent reading is claimed here.
