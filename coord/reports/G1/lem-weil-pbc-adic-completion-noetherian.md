## Worker report

The module `Sheaf.RingTheory.AdicCompletionNoetherian` states
`AdicCompletion.isNoetherianRing`, with `sorry` as its entire proof. No definitions or
proofs are added. Only the item's `lean` record is changed; no new or dependency nodes are needed.

Hypothesis and conclusion correspondence:

- The commutative ring `A` is `{A : Type u} [CommRing A]`; the explicit universe `u` permits
  every universe of rings. Commutativity is part of both recorded dependency definitions.
- “A is Noetherian” is `[IsNoetherianRing A]`, precisely the dependency's recorded notion
  that all ideals are finitely generated.
- “I ⊆ A an ideal” is `(I : Ideal A)`, with no properness or other restriction.
- “A^ is the I-adic completion” is `AdicCompletion I A`, using the dependency's actual
  Mathlib inverse-limit definition and its componentwise commutative ring structure.
- “Then A^ is a Noetherian ring” is `IsNoetherianRing (AdicCompletion I A)`.
  The completion is defined canonically, so no additional completion object or identification
  hypothesis is required.

Dependency declarations read and used:

- `def-weil-pbc-adic-completion`: `AdicCompletion`,
  `Mathlib.RingTheory.AdicCompletion.Basic`, lines 167–173; the compatible-family subtype
  of the quotients by `I ^ n • ⊤`. For the ring as its own module this ideal is `I ^ n`.
  Import `Mathlib.RingTheory.AdicCompletion.Algebra` supplies this definition and
  `AdicCompletion.instCommRing`, lines 97–101, the ring structure used by the conclusion.
  Also read the dependency's algebra structure and `AdicCompletion.evalOneₐ` signature
  and docstring; neither projection nor completeness predicate is needed in this lemma.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, lines 193–205, and the definition/docstring of
  `IsNoetherian`, lines 58–63. This is the dependency's recorded declaration and module.

Edge cases checked mathematically before drafting: the zero ring is allowed (no
`Nontrivial A` assumption); `I = ⊥` gives the original ring as its completion; `I = ⊤`
gives the zero ring as its completion. Neither case requires excluding an ideal. The inverse
limit includes `n = 0`, whose quotient is the zero ring and does not alter compatibility.
The proof's finite generating family may be empty. No characteristic, domain, localness,
separatedness, or completeness assumption is imposed on `A`.

Source checked: https://stacks.math.columbia.edu/tag/0316 (Lemma 10.97.6), including its
second proof. The local `literature/stacks-project/algebra.tex` is absent on this machine,
so the official Stacks page was read instead. It confirms exactly these hypotheses and
conclusion. The declaration docstring records all four node proof steps and their node IDs.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches performed (2026-10-11):

- `msearch.py leanfinder`, query “The adic completion of a Noetherian commutative ring with
  respect to any ideal is Noetherian”: eight hits, including
  `AdicCompletion.flat_of_isNoetherian`, Hausdorffness and completeness notions, and Rees
  algebra Noetherianity; none is the target theorem.
- `msearch.py loogle`, query `AdicCompletion, IsNoetherianRing`: twelve hits about exactness,
  flatness, tensor-product comparison, and local-ring/completeness instances; no match.
- `msearch.py grep`, query `IsNoetherianRing.*AdicCompletion|isNoetherianRing`, restricted
  to `RingTheory/AdicCompletion`: eleven hits, all hypotheses or unrelated consequences;
  no Noetherianity theorem for the completion.
- Direct `rg` of Mathlib for `isNoetherianRing.*AdicCompletion|AdicCompletion.*isNoetherianRing`
  finds only uses of ideal finite generation in `AdicCompletion/LocalRing.lean`.
- Direct `rg` of `WeilConjectures` and `lean/Sheaf` for `AdicCompletion`, adic Noetherianity,
  and `isNoetherianRing`: upstream imports and unrelated Noetherianity results; project
  definitions of analytically unramified rings and G-rings, but no matching theorem.
- `grep -rn` of upstream `WeilConjectures` for the item ID: no hit.
- Direct `rg` of `dag/lean_names_upstream.json` for the proposed full declaration and
  completion Noetherianity: no hit. The namespace/name checks in the adic-completion
  Mathlib sources and project ring-theory sources find no `AdicCompletion.isNoetherianRing`.

- `msearch.py leansearch`, query “The I-adic completion of a Noetherian ring is
  Noetherian”: service unavailable (Internal Server Error); no verdict inferred.

Validation: `scompile.py G1 lem-weil-pbc-adic-completion-noetherian` compiled the module
on the server in 1.2 seconds with exit code 0 and no warnings. Delivery preflight follows.

## Second reading by G1

I reread the node statement, its Stacks source place, both dependency nodes, and the
Lean module line by line. The correspondence is:

- The node's object “a Noetherian ring $A$” is rendered by `{A : Type u}` with
  `[CommRing A] [IsNoetherianRing A]`. `IsNoetherianRing` is the exact dependency
  notion (all ideals finitely generated); the universe is explicit and unrestricted.
- The node's ideal $I \subseteq A$ is the explicit `(I : Ideal A)` argument. No
  properness, finiteness, characteristic, domain, or nontriviality assumption is added.
- The node's $I$-adic completion $A^\wedge$ is exactly `AdicCompletion I A`, the
  declaration recorded by `def-weil-pbc-adic-completion`, with Mathlib's induced
  commutative ring structure.
- The conclusion “$A^\wedge$ is Noetherian” is exactly
  `IsNoetherianRing (AdicCompletion I A)`, with the same quantifier order.

The source is Stacks Project, Commutative Algebra, Tag 0316 (Lemma 10.97.6),
second proof. Its standing assumptions are a commutative Noetherian ring and an
arbitrary ideal, matching the binders. The declaration docstring records the four
source proof steps and their dependency node IDs: finite generators of $I$;
surjection from multivariate formal power series; Noetherianity of that source; and
Noetherianity of a surjective image.

I checked edge cases: the zero ring is allowed; `I = \u22a5` and `I = \u22a4` are allowed;
the finite generating family may have `n = 0`; the completion's index includes
`n = 0`; and no characteristic or separatedness hypothesis is imposed. These cases
are not excluded by the Lean binders.

I searched Mathlib and the project with LeanSearch, LeanFinder/Loogle, and direct
`rg`/grep for `AdicCompletion` together with `IsNoetherianRing` (and searched the
upstream declaration-name index). The hits were flatness, completeness,
Hausdorffness, and unrelated power-series results; no declaration of this theorem
exists. The recorded dependency declarations are therefore used directly, with no
private duplicate definitions and no new dependency modules.

No mismatch was found. The worker module already had the exact node statement, a
proper module and declaration docstrings, explicit universes, and only the required
`sorry` proof. I changed no Lean code or node fields; this section supplies the
independent second reading required for delivery.
