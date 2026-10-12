## What changed

The original declaration
`AlgebraicGeometry.Scheme.Hom.exists_section_restricting_to_fiber_idempotent`
now has a complete Lean proof from two strictly smaller parts of its existing argument:
locally Noetherian lifting (Steps 1–4) and descent of a fibre idempotent to a locally
Noetherian model (Steps 5–8). Each is stated in its own new module and node.
The main module proves Step 9, including localization on the original base, pullback
of a section, transport across an open immersion's section isomorphism, and the
composition identities showing that its fibre restriction is the original idempotent.
The original signature, public imports, and existing docstrings are unchanged.
The parent node now records this decomposition and the actual pullback argument.
No existing module besides the assigned item is changed.

Verification: all three sandbox modules compile together in import order through
lcompile.py, without warnings. The main proof uses no local admissions.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Hom.exists_section_restricting_to_fiber_idempotent`
(node `lem-weil-pbc-stein-fibre-idempotent-image`). No holes remain in the item.

Added two holes, each a public theorem with its whole proof `by sorry`:

- `AlgebraicGeometry.proper_fibre_idempotent_image_noetherian`, node
  `lem-weil-pbc-stein-fibre-idempotent-image-noetherian`, module
  `Sheaf.AlgebraicGeometry.ProperFibreIdempotentImageNoetherian`.
  This is only the locally Noetherian case, with a detailed formal-functions proof in
  its docstring and the original Steps 1–4 in its node.
- `AlgebraicGeometry.proper_fibre_idempotent_descent`, node
  `lem-weil-pbc-stein-fibre-idempotent-descent`, module
  `Sheaf.AlgebraicGeometry.ProperFibreIdempotentDescent`.
  This produces a Noetherian model and a descended idempotent with compatible maps;
  it asserts no lifting to a section on a neighbourhood. Its docstring and node
  explain affine localization, proper approximation, fibre limits and section descent.

This is a decomposition, not a sorry-free proof of the mathematical result: one hole
closed and two added, net -1. The actual section pullback and equality argument is proved.
No arbitrary witness is used to define public data. The local section transport is the
inverse of a proved open-immersion isomorphism.

Edge cases checked in the statements: no nontriviality of the idempotent or nonemptiness
of a fibre is assumed; zero, one and the empty fibre cause no exception. The original
base is not assumed affine, quasi-compact, or Noetherian. The descent statement retains
an open neighbourhood W and maps only from its restrictions, so it does not incorrectly
require the entire original morphism to map to a finite-type model.

## No longer needed

Removed these six direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.FormalFunctionsStalk`
- `Sheaf.AlgebraicGeometry.LimitFibreProducts`
- `Sheaf.AlgebraicGeometry.LimitResidueField`
- `Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents`
- `Sheaf.AlgebraicGeometry.ProperBasic`
- `Sheaf.AlgebraicGeometry.ProperLimitNoetherian`

Their planned uses are confined to the two residual modules. LimitResidueField is
already imported publicly by LimitFibreProducts and needs no separate import.
No original mathematical dependency node or module is claimed globally pruned: the
Noetherian and descent subarguments still use the original route. The main node's
proof_deps now consists of the two new nodes and def-pc-scheme-fibre. No unit statement
or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the original statement or proof plan. The former
indirect imports provide substantial machinery, but do not directly supply the
locally Noetherian lifting argument or a single compatible descent package. These
are the two residual statements rather than renamed copies of the entire claim.

The local copy of literature/stacks-project/perfect.tex is absent. I checked the
current source at https://stacks.math.columbia.edu/tag/0G7X; it follows the same two
parts and final pullback as the node. The original node's historic section number
21.16.1 differs from the current 36.32.7, but its tag and mathematics agree.
LeanSearch was attempted separately for both parts and returned service unavailable
(Internal Server Error); no absence verdict is inferred from those failures.
LeanFinder, Loogle and source grep supplied the available search evidence.

## New nodes

`lem-weil-pbc-stein-fibre-idempotent-image-noetherian` states the locally Noetherian
case only, in ProperFibreIdempotentImageNoetherian. Its proof is the original Steps 1–4
and cites nilpotent idempotent lifting, formal functions, and completion modulo the
maximal ideal. Its source and full proof are also in the declaration docstring.

`lem-weil-pbc-stein-fibre-idempotent-descent` states the approximation/descent portion
only, in ProperFibreIdempotentDescent. Its proof is the original Steps 5–8 plus the
canonical commuting-map identifications; it does not assume or conclude any lifting
of the idempotent to a neighbourhood section. Both nodes retain the parent's chapter,
unit and blueprint ancestor. No change record is needed: no existing interface changed.

## Second reading by P3

1. **Existing declarations and statements.** I diffed the delivered item against the
repository version. The theorem signature is unchanged; only its proof and proof-only
imports changed. The two added declarations are new split-off statements, and their node
statements match their Lean types.

2. **Proof and kernel checks.** I compiled all three sandbox modules with
`lcompile.py --all`. The parent theorem has no local admission. The only remaining
`sorry`s are the two named split-off theorems, each with a complete source-based proof
docstring; no forbidden declarations or hollow definitions occur.

3. **Truth and strength of split statements.** I checked the locally Noetherian statement
against Steps 1--4 of Stacks Tag 0G7X and the descent statement against Steps 5--8.
The former retains the original fibre-section conclusion and required hypotheses; the
latter supplies exactly the model, maps, commuting identities, and descended idempotent
needed by the parent, without asserting the parent conclusion under another name. Empty,
zero, and unit idempotents introduce no exceptional assumptions.

4. **Shortest route and pruning.** The parent proof uses the two strictly smaller nodes,
then Mathlib open-immersion section transport and appLE composition. I verified that the
six former direct proof imports are no longer referenced by the parent and are retained
only through the residual modules. The node proof and `proof_deps` records agree with
these imports and uses.

5. **Unit route and DAG consistency.** The parent and both split nodes remain in
`sec-proper-base-change` and unit `sk-thm-p1`; no unit statement or realized step is
bypassed. The new node metadata, declarations, docstrings, and module paths agree.

I also normalized a duplicated space before `:=` in the parent theorem line; this is
formatting only and does not alter its declaration.
