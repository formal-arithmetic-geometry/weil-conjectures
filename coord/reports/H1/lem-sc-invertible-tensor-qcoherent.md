## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent` states
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor_integer_power`. It takes a
scheme `X`, quasi-coherent module `F`, invertible module `L`, and an integer `n`.
The conclusion is that `F` tensor the integer power of `L` is quasi-coherent. The
`if h : 0 ≤ n` clause renders the nonnegative power as `L.tensorPow n.toNat`; its
negative branch renders the stipulated negative power as `(Lᵛ).tensorPow (-n).toNat`.
The typeclass binders render exactly the quasi-coherence and invertibility
hypotheses. The tensor is the monoidal tensor on `X.Modules`, the sheaf of
`O_X`-modules tensor product.

The declaration uses the recorded invertible-module notion
`AlgebraicGeometry.Scheme.Modules.IsInvertible` from
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`, and Mathlib's
`SheafOfModules.IsQuasicoherent` (the project declaration attached to
`pqf-def-coherent` is `AlgebraicGeometry.RingedSpace.IsCoherent`). Tensor powers,
duals, and invertibility closure facts come from
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`; the tensor
construction is the monoidal tensor supplied by `def-pur-sheaf-tensor-product`.

Edge cases checked: `n = 0` selects `L.tensorPow 0`, the monoidal unit; `n = 1`
selects `L.tensorPow 1`; `n = -1` selects the tensor power zero of `Lᵛ`; and
there is no restriction on the scheme (including the empty scheme) or on the
integer. The proof is intentionally `sorry` at stage 2. No statement is
believed false.

Searches for an existing exact declaration:

* `msearch.py ... leanfinder "tensor product quasi-coherent module invertible module integer tensor power scheme"` returned only generic Picard/module tensor results and no sheaf theorem.
* `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj, Scheme.Modules.tensorPow"` returned no hits (the source identifier is unavailable to Loogle).
* `msearch.py ... grep "isQuasicoherent_tensorObj|tensorPow" AlgebraicGeometry` returned no match; direct `rg` in the source found `isQuasicoherent_tensorObj` and `IsInvertible.tensorPow` in `ProjectionFormula.lean`, but no integer-power theorem. Direct Mathlib grep found no corresponding scheme theorem.
* Direct searches of `WeilConjectures/` and `lean/Sheaf/` found no declaration with an integer tensor-power conclusion.

## Earlier second reading (a previous round; superseded)

I reread the node and module signatures independently. The scheme, quasi-coherent
module, invertible module, and integer binders are all present. The two branches
of the `if` are exactly the node's positive and dual-defined negative powers, and
the conclusion asserts quasi-coherence of the complete tensor product. No
hypothesis or edge case was added or omitted.

## Second reading by H1

I opened the node and the complete Lean file and matched each item. The introduced
scheme is `X : Scheme.{u}` and the Lean binder `{X : Scheme.{u}}` renders the
node's arbitrary scheme, including the empty scheme. The modules are `F L :
X.Modules`, the node's mathcal F and mathcal L. The hypotheses are
`[F.IsQuasicoherent]` and `[L.IsInvertible]`; these are exactly the recorded
quasi-coherence and `Scheme.Modules.IsInvertible` notions, with no Noetherian,
separation, finiteness, characteristic, or field assumptions.

The integer is `(n : ℤ)`. The conclusion is
`(tensorObj F (if h : 0 ≤ n then L.tensorPow n.toNat else
(dual L).tensorPow (-n).toNat)).IsQuasicoherent`: `tensorObj` is the
`def-pur-sheaf-tensor-product` monoidal tensor, the nonnegative branch is the
natural tensor power, and the negative branch is the natural tensor power of
 the dual. Thus it states precisely the node's tensor product and its stipulated
negative-power convention; the quantifier order is unchanged. The declaration
has only a `sorry` proof, as required at stage 2, and its docstring gives both
proof steps and their source nodes.

I checked edge cases directly from the expression: `n = 0` takes
`L.tensorPow 0`, `n = 1` takes `L.tensorPow 1`, and `n = -1` takes
`(dual L).tensorPow 1` (the source convention's dual power). No index set,
scheme nonemptiness, or characteristic is assumed, so the empty scheme and
zero modules remain covered. The universe is the scheme's universe and no
independent universe is introduced.

Searches found no exact declaration in Mathlib, `WeilConjectures`, or the
project's `lean/Sheaf`; `ProjectionFormula.isQuasicoherent_tensorObj` only
covers one invertible factor, and `IsInvertible.tensorPow` only natural powers.
The recorded dependency declarations and the tensor construction were read;
no missing notion or unusable dependency required a new module. I found no
mismatch and made no source or statement change. The module compiled cleanly
with `scompile.py` (the only permitted diagnostic is the intentional `sorry`).
