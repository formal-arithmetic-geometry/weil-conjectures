## What changed

Proved `AlgebraicGeometry.Etale.isIso_etaleLowerShriekBaseChangeMap` by unfolding the
base-change map and applying the existing étale base-change isomorphism theorem for the
flipped pullback square. The `conjugateEquiv_symm_iso` instance transfers the isomorphism
to the conjugate defining the lower-shriek map. Removed proof-only imports for the inverse
image and module-linearity lemmas, the base-change square module, and the étale map module.

## Proved and sorry left

The sole theorem `AlgebraicGeometry.Etale.isIso_etaleLowerShriekBaseChangeMap` is proved;
no `sorry` remains.

## No longer needed

Removed proof-only imports:
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`

The last two remain available through the public import defining the map. Removed direct
planned proof dependencies (no claim that they are globally unreachable):
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-restriction-injectives`
- `prop-weil-pbc-inverse-image-modules-exact`
- `def-weil-pbc-composite-adjunction`
- `def-weil-pbc-cartesian-square`
- `def-weil-pbc-underived-exchange`
- `lem-weil-pbc-underived-exchange-module-linear`
- `def-weil-sheaf-of-modules-category`

Retained the map definition, the existing underived exchange restriction result (the
upstream theorem combines its recorded declarations for module coefficients), and the
conjugate-isomorphism leaf, which typeclass synthesis uses.

## Where the brief, the DAG or earlier work was wrong

The planned four-step adjunction and module-linearity argument was unnecessary: the source
library already proves the required module-valued étale base-change exchange isomorphism,
and the target follows immediately by the conjugate isomorphism instance.

## Second reading by P2

1. Compared the sole delivered module against the repository using `diff`: the existing
   theorem signature and docstring are byte for byte unchanged. No definitions, public
   imports, or other declarations changed; no change record is needed. Verdict: pass.
2. Compiled the module locally with `lcompile.py`, without errors or warnings. A scratch
   copy with `#print axioms AlgebraicGeometry.Etale.isIso_etaleLowerShriekBaseChangeMap`
   reports only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, axiom,
   unsafe declaration, opaque declaration, external implementation, or hollow definition
   in the delivered module. Verdict: pass.
3. No statements were split off and no new nodes were introduced. Read the existing
   upstream exchange theorem and Mathlib conjugation instance; the square flip matches
   the map's definition, and the result applies without any additional assumptions on
   the scheme map or coefficient ring. Searched for exchange and conjugation results
   with `rg` and `msearch.py grep`; these are the existing results used by the proof.
   Verdict: pass; no new edge-case claims require testing.
4. The proof takes the existing upstream isomorphism immediately after unfolding the
   target map, then uses inverse conjugation. The imports are minimal: the public import
   supplies the statement, and the single private import supplies the exchange theorem.
   Checked `dag/units/sk-thm-p1.json`, `sk-thm-iff.json`, and `sk-def-exchange.json`:
   none of the removed nodes realizes a unit statement or proof step. The simplification
   is below the unit level and preserves the unit route. Verdict: pass after completing
   the explicit pruning list.
5. Checked the node's unchanged statement and Lean record, and its `proof`, `proof_deps`,
   and `proof_origin` against the actual proof. Restored the existing exchange-restriction
   node and conjugation leaf to the proof dependencies and step uses: both are used by
   the upstream proof or final typeclass synthesis. The proof origin points to the exact
   upstream theorem. Verdict: pass after metadata repair.

Second reading changed only metadata and reporting: restored two used proof dependencies,
listed all eight removed direct planned dependencies, and recorded these checks. The Lean
proof was correct and needed no edit.
