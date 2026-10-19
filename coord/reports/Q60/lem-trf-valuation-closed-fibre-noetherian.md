## Worker report

The module `lean/Sheaf/TraceFormula/ValuationClosedFibreNoetherian.lean` states
`Algebra.valuation_closed_fibre_noetherian`.  Its hypotheses are `[CommRing A]`,
`[IsDomain A]`, and `[ValuationRing A]`, rendering that `A` is a valuation ring;
`[CommRing B]` and `[IsLocalRing B]`, rendering the local target ring;
`[Algebra A B]`, `[Algebra.EssFiniteType A B]`, and
`[IsLocalHom (algebraMap A B)]`, rendering the essentially finite type local
homomorphism.  The first conclusion is `IsNoetherianRing (B ⧸ J)`, where
`J` is written explicitly as
`Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)`, the extension of
`\mathfrak m_A` to `B`, so this is `B/\mathfrak m_A B`.

The second conclusion is a universal quantifier over every universe-`w` type
`N` with `[AddCommGroup N]`, `[Module B N]`, and `[Module.Finite B N]`.  It states
`Module.FinitePresentation (B ⧸ J)
(N ⧸ (J • (⊤ : Submodule B N)))`.  The quotient submodule is the extended
ideal action, rendering `N/\mathfrak m_A N`; Mathlib's quotient-module
instance supplies its `(B ⧸ J)`-module structure.  The two conclusions are
joined by `∧`, exactly as in the node statement.

Dependencies used by the statement are recorded Mathlib declarations:

* `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType`.
* `def-weil-finitely-generated-module`: `Module.Finite`.
* `def-sc-finitely-presented-module`: `Module.FinitePresentation`.
* `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`.

The imports are `Mathlib.RingTheory.Valuation.ValuationRing`,
`Mathlib.RingTheory.EssentialFiniteness`,
`Mathlib.RingTheory.LocalRing.Basic`,
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`,
`Mathlib.Algebra.Module.FinitePresentation`, and
`Mathlib.Algebra.Module.Torsion.Basic`; these provide the recorded declarations,
maximal ideals, and quotient-module action.

Edge cases checked: a valuation ring may be a field (then its maximal ideal is
`⊥`); `B` and `N` may be zero when the stated typeclass assumptions allow them;
no nonzero or finite-rank hypothesis is imposed; the module universe is an
explicit `Type w`; and the extended ideal quotient is used so the canonical
`B/\mathfrak m_A B` and `N/\mathfrak m_A N` actions are retained.

Searches made before writing:

* `msearch.py Q60 lem-trf-valuation-closed-fibre-noetherian leanfinder` for
  “The closed fibre quotient of an essentially finite type local algebra over a
  valuation ring is Noetherian”: only general finiteness/localization results,
  no exact statement.
* `msearch.py ... loogle` for `Algebra.EssFiniteType, IsNoetherianRing`: only
  `Algebra.EssFiniteType.isNoetherianRing`, which assumes a Noetherian base and
  is not this valuation-ring statement.
* `msearch.py ... grep` for
  `EssFiniteType.isNoetherianRing|essFiniteType.*[Qq]uotient|essFiniteType.*[Ff]iber`:
  related Mathlib declarations but no exact match.
* `rg` over `lean/Sheaf` and `WeilConjectures/` for valuation/closed-fibre
  Noetherian declarations: no exact project or upstream declaration.
* `rg` over `dag/nodes` for the item and its theorem name: no existing Lean
  record or duplicate notion.

The file compiles cleanly with `scompile.py`; the only proof is the required
`sorry`.  No `STATEMENT-DISPUTED` flag or statement correction is required.

## Second reading by Q60

I independently compared the node sentence clause by clause with the module.
`A` is a commutative domain carrying `ValuationRing`; `B` is a commutative local
ring carrying the algebra structure; essential finite type and localness of the
algebra map are both present.  The first conjunct is exactly Noetherianity of
`B` modulo the mapped maximal ideal.  The universal second conjunct quantifies
over every finite `B`-module and uses the quotient by the same extended ideal,
with `Module.FinitePresentation` over the closed-fibre ring.  No hypothesis or
clause was added, dropped, weakened, or strengthened, and the zero-module and
field valuation-ring cases remain admitted.
