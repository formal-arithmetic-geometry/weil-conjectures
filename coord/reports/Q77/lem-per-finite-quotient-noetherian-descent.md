## Worker report

Stated `RingHom.isNoetherianRing_of_injective_of_finite` in
`Sheaf.RingTheory.FiniteInjectiveNoetherianDescent`. Its only proof is `sorry`.
No new definition, dependency module, or statement correction is needed. The node
copy changes only `lean`; its reviewed stage-1 split remains intact.

The previous worker's stale-assignment conclusion confused stage-1 splitting with
stage-2 statement writing. Q04 reviewed the split on 2026-10-19, but the current
node has no `lean` record or `reviewed_lean`. This delivery states that approved
node and does not split it again.

Clause-by-clause correspondence:

- Commutative rings B and A: `{B : Type u} {A : Type v} [CommRing B] [CommRing A]`,
  with explicitly declared, independent universes `u v`.
- The given ring homomorphism i:B→A: `(i : B →+* A)`.
- Injectivity: `(hi : Function.Injective i)`.
- Noetherian target: `[IsNoetherianRing A]`, the dependency's recorded definition.
- A is finite as a B-module via i:
  `(hfinite : @Module.Finite B A _ _ (@Algebra.toModule B A _ _ i.toAlgebra))`.
  `RingHom.toAlgebra` has algebra map i and scalar action b•a = i(b)*a;
  `Algebra.toModule` supplies exactly this module. No arbitrary action is quantified.
- Conclusion: `IsNoetherianRing B`, with no further conditions or conclusions.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, abbreviation for `IsNoetherian B B`;
  the class requires every submodule (ideal) to be finitely generated.
- `def-weil-finitely-generated-module`: `Module.Finite` from
  `Mathlib.RingTheory.Finiteness.Defs`, defined by finite generation of the top
  submodule. Its special finite-ring and field clauses do not restrict its use
  for arbitrary commutative rings here.
- Canonical scalar action: `RingHom.toAlgebra`, `Algebra.toModule` from
  `Mathlib.Algebra.Algebra.Defs`. Their complete implementations were read.
- Proof dependencies are Mathlib leaves: `isNoetherian_pi` and
  `Submodule.FG.of_le` in `Mathlib.RingTheory.Noetherian.Basic`,
  `set_has_maximal_iff_noetherian` in `Mathlib.RingTheory.Noetherian.Defs`,
  and `zorn_subset` in `Mathlib.Order.Zorn`. The two proof-only modules use
  non-public imports. Their signatures were read; the docstring preserves all
  eight node proof steps, including their cited DAG ids.

Edge cases checked before drafting: the zero target forces the source to be zero
by injectivity; no Nontrivial or domain binder excludes it. Empty generating
families are allowed by Module.Finite (and in the proof docstring). Identity maps
are allowed. Nilpotent rings and nonreduced extensions are allowed. Independent
ring universes are preserved. Injectivity cannot be omitted: the quotient of
k[x_1,x_2,...] onto k is finite over its source while the source is not Noetherian.
Finiteness cannot be omitted: k[x,xy,xy²,...] embeds in the Noetherian ring k[x,y].
These confirm the hypotheses are substantive and exactly those in the node.

Searches, all through the prescribed msearch.py wrapper with Q77 and this item:

- LeanFinder: “An injective finite homomorphism into a Noetherian commutative ring
  has Noetherian source, Eakin Nagata theorem”. Eight hits. The closest were
  `IsNoetherianRing.of_finite` (ascent), `isNoetherian_of_injective` (requires
  Noetherianity of the target as a module over the source), and finite-type
  ascent results. None is the node.
- Loogle: `IsNoetherianRing, Module.Finite`. Twelve hits, including the same
  ascent theorem and `isNoetherian_of_isNoetherianRing_of_finite`, whose source
  is already assumed Noetherian. No exact match.
- Mathlib grep: `Eakin|Nagata|isNoetherianRing.*(finite|Finite)|[Nn]oetherian.*[Ii]nvariant`
  in RingTheory. Twenty-five hits, covering ascent and unrelated material.
- LeanSearch: “Noetherianity descends along an injective finite extension of
  commutative rings”. Eight hits on ascent, surjective images, or module
  injectivity; no exact match.
- Direct rg in upstream WeilConjectures and lean/Sheaf for Eakin, eakin, the
  item id, Noetherian descent, and the proposed declaration name. The relevant
  Eakin hit is a proof-plan mention in FiniteQuotientStrictLocalInvariants.lean,
  not a theorem giving this statement. Broad Nagata hits concern compactification
  or Nagata rings. No matching declaration.
- Exact-name/concept rg in dag/lean_names_upstream.json, Mathlib/RingTheory,
  upstream WeilConjectures, and lean/Sheaf confirms no declaration-name collision.

Source inspection: the node explicitly marks Eakin's paper and Matsumura §3
WANTED locally; no claim is made to have read them. The full reviewed eight-step
agent-written proof was read and copied into the theorem docstring. The local
Stacks examples.tex lines 1505–1512 invoke Eakin's theorem in this direction;
they are corroboration, not a proof source. No node fault or statement dispute
was found.

Validation: prescribed scompile.py compiled both its sandbox name and the real
library module name, each in 1.1 seconds, with no errors or warnings.

## Second reading by Q77

Author self-check only; independent review is supplied by the maintainer as in
the dispatcher brief. Re-read the complete node and generated module together:
the explicit i and its canonical multiplication action agree; finiteness is
module finiteness, not algebra finite type; target Noetherianity has not been
strengthened to source-module Noetherianity; source Noetherianity is the entire
conclusion. All universes and variables are bound. Both zero rings and arbitrary
commutative nonreduced rings remain in scope. No mismatch was found and no
statement was changed. The declaration docstring contains all eight proof steps.
