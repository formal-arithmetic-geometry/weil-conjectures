## Worker report

The module `Sheaf.CategoryTheory.OrdinaryHorizontalPastingTransport` states
`CategoryTheory.ordinaryHorizontalPastingTransport`, with its only proof `sorry`.
It introduces no definitions or helper theorems. The node changes only in `lean`.
No statement correction, disputed statement, dependency repair, or new node is needed.

Source read: Stacks Project Tag 0F7D,
`literature/stacks-project/more-etale.tex`,
`lemma-shriek-proper-and-open-compose-horizontal` (lines 2676 onward),
and the Local pairs paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/` +
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gluing.proof.md`.
The node isolates the categorical transport calculation, rather than asserting
Stacks' scheme-level theorem again. Its six-step proof is included in the docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The six categories and their primed counterparts are the twelve explicitly bound
  types `A B C D E F A' B' C' D' E' F'`, each with its own `Category` instance.
  All twelve object universes and all twelve morphism universes are independent
  and explicitly declared. There are no smallness, nonemptiness, abelian,
  adjunction, or faithfulness assumptions.
- The six functors `E_X` are `EA EB EC ED EE EF` with precisely the node's domains
  and codomains, for example `EA : A ⥤ A'` and `EE : E ⥤ E'`.
- The nine unprimed functors are `K L I J R P Q K₁₂ I₁₂` with exactly the
  endpoints in the node. Their nine primed counterparts use a trailing prime.
  Lean's `F ⋙ H` is the node's right-to-left `HF`.
- The nine invertible comparisons are `eR eP eQ eK eL eI eJ eK₁₂ eI₁₂`.
  Each has type `F ⋙ EY ≅ EX ⋙ F'`, meaning `EY F ≅ F' EX`.
- The composite-comparison convention is expanded in `hk hi ha hb hc`:
  `eF.hom.app M ≫ H'.map (eG.hom.app M)` is the forward component of
  the relevant composite comparison, with the input of `eF` adjusted to the
  first functor's object. Canonical associators have identity components;
  writing these equations at objects introduces no associativity assumptions.
- The unprimed compositor isomorphisms are `ck : K ⋙ L ≅ K₁₂` and
  `ci : I ⋙ J ≅ I₁₂`; their primed counterparts are `ck' ci'`.
  `hk` is exactly compatibility of `c_K` after evaluation at every `M : A`:
  `EE.map (ck.hom.app M) ≫ eK₁₂.hom.app M` equals the expanded `e_LK`
  followed by `ck'.hom.app (EA.obj M)`. `hi` is the identical compatibility
  for `c_I` at every `N : C`, with `EF`, `eJ`, `J'`, `eI`, and `ci'`.
- The three cells and their primed counterparts are
  `a : TwoSquare I R P K`, `b : TwoSquare J P Q L`,
  `c : TwoSquare I₁₂ R Q K₁₂`, and `a' b' c'`.
  Mathlib's `TwoSquare T L R B` is definitionally `T ⋙ R ⟶ L ⋙ B`;
  hence these are exactly `PI → KR`, `QJ → LP`, and `QI₁₂ → K₁₂R`.
  They are arbitrary natural transformations, with no invertibility imposed.
- `ha` expands respectedness of `a` at every `N : C`:
  `EB.map (a.app N)` followed by `eK` and `K'.map eR` equals `eP`
  followed by `P'.map eI` and `a'.app (EC.obj N)`.
  `hb` expands respectedness of `b` at every `M : D`: the target comparison
  uses `eL` then `L'.map eP`; the source comparison uses `eQ` then
  `Q'.map eJ`, followed by `b'.app (ED.obj M)`.
  `hc` expands respectedness of `c` at every `N : C`: the target comparison
  uses `eK₁₂` then `K₁₂'.map eR`; the source comparison uses `eQ` then
  `Q'.map eI₁₂`, followed by `c'.app (EC.obj N)`.
  Each is the node's `e_H ∘ E(t) = (t' E_X) ∘ e_F`.
- `hstrict` quantifies over every `N' : C'`. Its left side is
  `Q'.map (ci'.hom.app N') ≫ c'.app N'`; its right side is
  `b'.app (I'.obj N') ≫ L'.map (a'.app N') ≫ ck'.hom.app (R'.obj N')`.
  This is precisely the component expansion of the assumed primed pasting
  equation; natural-transformation extensionality makes the formulations equivalent.
- The final explicit `N : C` is arbitrary. The conclusion is exactly
  `EE.map (Q.map (ci.hom.app N) ≫ c.app N) =
   EE.map (b.app (I.obj N) ≫ L.map (a.app N) ≫ ck.hom.app (R.obj N))`.
  Both sides remain inside `EE.map`: no unprimed equality is asserted.

Dependency declaration read and used: `def-weil-pbc-adjunction-mate` is a Mathlib
leaf recorded at `CategoryTheory.mateEquiv`, module
`Mathlib.CategoryTheory.Adjunction.Mates`. I read its full signature, docstring,
and component construction (Mates.lean lines 55–106), together with
`CategoryTheory.TwoSquare` and its docstring in
`Mathlib/CategoryTheory/Functor/TwoSquare.lean` lines 39–64.
The module publicly imports the recorded Mates module and uses its square
notation; as the node explicitly requests, no adjunction is needed here.
The proof dependency list is empty, so there are no further proof imports.

Edge cases checked before writing: if `C` is empty, the result has no inputs and
is vacuous without excluding that category. Identity comparisons and identity
compositors reduce to ordinary component pasting. If the primed categories are
terminal and the comparison functors erase morphism distinctions, the theorem
only asserts equality after `EE`, so it remains valid without faithfulness.
Noninvertible and zero cells are permitted: cancellation concerns only the
invertible target comparison. Each functor and equation has the prescribed
endpoints. Independent category universes impose no equality of sizes.

Searches actually run:

- `msearch.py leanfinder` with query “Transport a horizontal pasting equation of
  natural transformation squares through nine coherent natural isomorphisms
  without faithful functors”: eight hits, including `CatCommSq.hComp_iso_hom_app`,
  `TwoSquare.hComp`, `TwoSquare.hComp_app`, and `TwoSquare.hCompVCompHComp`.
  They construct pasting or give its components/interchange, not this transport
  implication with prescribed outer cells and nine comparisons.
- `msearch.py loogle` query `CategoryTheory.TwoSquare.hComp, CategoryTheory.NatIso`:
  diagnostic “unknown identifier 'CategoryTheory.NatIso'”, not an absence result.
  Corrected query `CategoryTheory.TwoSquare.hComp`: eleven hits, including the
  hComp construction, its component lemma, interchange, and mate-pasting results.
  Inspection of TwoSquare.lean confirms these are not the present statement.
- `msearch.py leansearch` query “Coherent natural isomorphisms transport a horizontal
  natural transformation pasting equation”: eight hits, including
  `NatTrans.naturality_2`, `NatTrans.hcomp`, pseudonaturality and monoidal transport;
  none states this implication.
- `msearch.py grep` query `horizontal.*transport|transport.*hComp|ordinary_horizontal`
  in `CategoryTheory`: zero hits.
- `rg` of the same pattern and the item id in `lean/WeilConjectures` and `lean/Sheaf`
  finds a private `ordinary_horizontal_transport` in
  `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` (lines 550–607), plus
  distinct geometric inverse-mate transport statements upstream. I read the whole
  private theorem, its surrounding binders and proof, and the
  `OrdinarySquareComparison` interface at
  `VaryingRingOrdinaryClopenEvaluation.lean` lines 61–79. The private theorem
  matches the calculation but is not a public attachment, as also recorded in
  the stage-1 review. The new theorem makes no copy of its comparison structure:
  respectedness is stated directly as the node's equations.
- The proposed public name was searched in `dag/lean_names_upstream.json`,
  Mathlib, and the project; no declaration exists with that name.

Validation: the prescribed `scompile.py` compiled the file both as a sandbox
module and under its library module name, each in 1.3 seconds, without errors
or warnings. No proofs were supplied in this stage. The expected `sorry`
remains only at `CategoryTheory.ordinaryHorizontalPastingTransport`.

## Returned-delivery validation (2026-10-21)

The return on immutable head `4436f4fad138` reported that unit
`sk-prop-sfb-qlbar-colimit-x` realized the missing node
`lem-sfb-qlbar-point-abelian-colimit`. That node now exists in the current
shared repository. The prescribed first dry run of the retained packet passes
server preflight and compilation (`8d6dfb90b05`); no source or statement repair
is required. Following the repair brief's retained-packet instruction, the
Lean module and node record are preserved. Compared with the current node,
only `lean` differs. The signature matches the source verbatim, all universes
and variables are explicitly bound, and the conclusion remains equality after
`EE.map` without any faithfulness hypothesis. A fresh `scompile.py` run checked
both the sandbox and library module names in 1.3 seconds each, cleanly.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
