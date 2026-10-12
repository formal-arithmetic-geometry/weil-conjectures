## What changed

Marked `AlgebraicGeometry.Etale.exists_isFinite_cohomologyMap_eq_zero_of_henselianRing`
with `STATEMENT-DISPUTED` and a counterexample. Its signature, proof placeholder, visibility,
and every other declaration are unchanged. No imports or definitions change. This is a
statement-dispute delivery, not a proof or decomposition.

The counterexample is on an affine Noetherian scheme and already has finite coefficients,
so neither the constructibility correction nor coefficient-ring generalization removes it.

## Proved and sorry left

Holes closed: none. Holes added: none.

The two existing holes remain:

- `AlgebraicGeometry.Etale.exists_isFinite_cohomologyMap_eq_zero_of_henselianRing`
  (`lemma-weil-pbc-finite-cover-killing`), disputed below.
- `AlgebraicGeometry.Etale.exists_mono_map_eq_zero_of_henselianRing`
  (`lemma-weil-pbc-gabber-effacement`), untouched.

A separate scratch check, not included in the delivery, proves in Lean the precise
long-exact-sequence obstruction used below: if the pulled-back degree-zero section of
the quotient term does not extend to the middle term, its pulled-back boundary is nonzero.
It uses `cohomologyMap_comp_extClass` and `Ext.covariant_sequence_exact₃`.
The geometric example itself is justified in words, rather than claimed as a formal
Lean refutation.

## No longer needed

None. No import, node, or module is removed. The unit's statement and realized steps
are unchanged. In particular this delivery does not replace Gabber effacement by finite
geometric killing. Searching the Lean sources finds no use of the disputed declaration
outside its definition and the module documentation, so its removal or correction is
not presently forced on a downstream proof.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: finite covers cannot kill all positive-degree classes of constructible
sheaves, even with the monicity condition on the unit and for the henselian pair `(A, 0)`.

Here is a counterexample satisfying the exact hypotheses.
Let `k` be an algebraically closed field, let `A = k[t]`, let `I = 0`, and let
`X = Spec A`. The library proves `HenselianRing A ⊥` for every commutative ring.
Take the finite coefficient ring `Λ = ℤ/2` (lifted to the required coefficient universe).
Put `D = {0,1}`, with its reduced closed subscheme structure, and
`U = X \ D`. Write `j : U → X` and `d : D → X` for the inclusions. Set
`C = j_! Λ_U`. This is constructible: the three strata `U`, `{0}`, and `{1}`
are constructible and locally closed; its restrictions are respectively constant of
rank one, zero, and zero. Thus it satisfies the library's current stratification-based
`IsConstructibleSheaf`, not merely an older defective version of that predicate.

The open-closed exact sequence is

`0 → C → Λ_X → d_* Λ_D → 0`.

For the underlying abelian sheaves this is Stacks Tag 095L; extension by zero for module
sheaves agrees with its underlying abelian version (Stacks Section 03S2).
Let `s ∈ H⁰(X,d_* Λ_D) = Λ × Λ` be `(0,1)` and let `c = δ(s) ∈ H¹(X,C)`.
Since `X` is connected, `H⁰(X,Λ_X) = Λ`, and restriction to the two points is diagonal.
Exactness therefore gives `c ≠ 0`. With `I=0`, the quotient-spectrum map in the disputed
theorem is an isomorphism, so this is also a class of precisely the closed-fibre group
appearing in its signature.

Suppose a finite morphism `h : V → X` satisfied the conclusion. Monicity of the unit
`C → h_* h^* C` implies that the geometric generic fibre of `h` is nonempty: at the
geometric generic point, `C` has stalk `Λ ≠ 0`, whereas the target stalk would be zero
if the fibre were empty. This is the finite direct-image stalk formula already used by
the node. Choose a point of `V` over the generic point, and let `W` be its connected
component. The finite scheme `V` over `k[t]` is Noetherian, so its finitely many connected
components are open and closed. Hence `W → X` is finite. Its image is closed and contains
the generic point; it is therefore all of `X`. In particular `W` has a point over `0`
and a point over `1`.

Pulling back the open-closed sequence is exact. Its middle term is `Λ_V`, and its
quotient is the constant sheaf on `D_V = V ×_X D`, pushed forward to `V`; finite closed
pushforward commutes with base change. The pulled-back section `s_V` has value `0` on
`h⁻¹(0)` and value `1` on `h⁻¹(1)`. A global section of `Λ_V` is a locally constant
function on `V`; it is constant on the connected component `W`. Since `W` meets both
fibres, no such section can restrict to `s_V`. Exactness of the cohomology sequence gives
`δ_V(s_V) ≠ 0`. Naturality of the boundary identifies this with `h^* c`, contradicting
the asserted killing. The same argument applies after the harmless quotient-spectrum
and fibre-product isomorphisms for `I=0`. It does not require the extra finite-presentation
hypothesis, so that hypothesis cannot repair the statement.

Sources checked: [Stacks 095L](https://stacks.math.columbia.edu/tag/095L),
[extension by zero, 03S2](https://stacks.math.columbia.edu/tag/03S2),
[09ZD](https://stacks.math.columbia.edu/tag/09ZD), and
[09ZE](https://stacks.math.columbia.edu/tag/09ZE).
The local Stacks TeX referred to in the DAG is absent on this machine, so the official
Stacks pages were read instead. The counterexample is an original argument from their
exact-sequence and stalk formulas.

The false inference in the node is its first sentence: an integral strictly-local cover
is said to kill `c` for arbitrary constructible `C`. The supplied 09ZD theorem only gives
killing for finite **constant** coefficients. In the counterexample above, any integral
surjective cover also has a connected component dominating `X`, so the same obstruction
persists. The node's finite-stage continuity step cannot repair an initial vanishing that
is false. This is a node-level error; no fixed unit statement is disputed.

Stacks 09ZE correctly kills a class after changing its coefficient sheaf by a
monomorphism. In this example the monomorphism `C → Λ_X` already kills `c` by exactness.
Thus the counterexample does not dispute Gabber effacement or the pair-comparison target.
The effacement node's reviewed nine-step proof explicitly no longer uses the obsolete
finite-cover-killing node; it uses finite covers only for constant summands, followed by
monomorphisms of coefficient sheaves and pushouts. This route remains appropriate.

Before finding the counterexample I explored bounded torsion approximation of the generic
`Λ`-module effacement theorem. The supplied finite-ring constructible-representation
modules do not directly cover arbitrary `Λ`. The generic affine-closed injective
acyclicity theorem cannot be imported as a shortcut: `import_direction.py may` correctly
reports that it already depends on Gabber. No circular import or replacement hole was
introduced.

## Second reading by M1

1. **Interface comparison: pass.** A full diff against the repository shows only the
   eight-line `STATEMENT-DISPUTED` comment before the finite-cover-killing theorem.
   All existing declaration signatures, visibility, definitions, proof bodies and imports
   are byte-for-byte unchanged. There are no new declarations or change records.
2. **Lean and trust check: pass for a dispute delivery, not a completed proof.** The
   delivered module compiles locally without errors or warnings. The two existing named
   theorem holes listed above remain, with no new holes and no forbidden declarations or
   hollow definitions. A scratch copy prints axioms of the auxiliary lemmas and all main
   theorems; only the permitted axioms and existing `sorryAx` dependencies occur. The
   separate boundary-obstruction scratch theorem also compiles. Neither scratch file is
   delivered. The geometric counterexample is an informal refutation, not a Lean proof
   of the negation.
3. **Split statements and edge cases: pass; none split off.** Independently checked the
   exact hypotheses against `HenselianRing.bot` and the stratification-based
   `IsConstructibleSheaf`: `I = 0` is allowed and the three strata have finite locally
   constant restrictions. The constant sheaf with two elements represents locally
   constant functions, even on a nonreduced finite cover. The empty cover cannot satisfy
   monicity at the generic stalk. A component containing a point over the generic point
   is open and closed because the finite cover is Noetherian; its image is closed and
   contains the generic point, so it meets both endpoint fibres. The long exact sequence
   therefore certifies nonvanishing after every candidate finite cover. Checked official
   Stacks 095L, 03S2, 09ZD and 09ZE independently. The distinction between constant
   coefficient killing and coefficient-sheaf effacement is correct.
4. **Route and pruning: pass with no proof/pruning claimed.** Searched the library for
   callers of the disputed declaration; none occur outside its own module documentation.
   A fresh Mathlib search using `covariant_sequence_exact`, `constant` and `cohomology`
   confirms the available exact-sequence tools used by the scratch check. No shorter
   proof can establish the disputed false statement. No imports have become unused
   because of this comment-only delivery, and no old proof dependencies are removed.
   Read `dag/units/sk-thm-p1.json`; its statement and every `realized` step stay unchanged.
5. **DAG agreement: pass as an explicitly reported dispute.** Read both corresponding
   node records. The obsolete finite-cover node still records a proposed proof, whose
   first unsupported vanishing is identified above as false; the report does not claim
   this plan was realized. The nine-step effacement plan uses finite killing only after
   reduction to finite constant summands and remains appropriate. No node proof or
   dependency was silently changed, and no new node is needed for a dispute comment.

Second reading changed only this report: added the independent checks and verdicts.
The original dispute comment and counterexample are accepted unchanged. Holes closed:
zero of two; holes added: zero; split off: zero; modules pruned: none.
