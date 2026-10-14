## What changed

Proved `CategoryTheory.Functor.exactMateComparison_eq` with its original signature and
unchanged `exactMateComparison` definition. Added one proof-only import of
`Sheaf.CategoryTheory.DerivedMatePastedUnit`.

The proved local equation `comparison_unit` normalizes the four composition comparisons
using the existing right-derived factorization API. The final proof identifies the ordinary
mate via `hm`, obtains preservation of K-injectives for P from its exact left adjoint,
uses `rightDerived_ext` on RP followed by RF and `hed`, and applies the inverse mate law.
The intervening pasted-unit calculation is isolated as a general theorem for arbitrary
ordinary and derived natural transformations. It assumes no comparison ed, no mate
identification hm, no invertibility of either square, and no preservation of K-injectives by H.
It concludes a unit equation, leaving the comparison construction and uniqueness argument
in the original module. This is a decomposition, with net zero holes closed.

Both modules compile without errors or warnings using lcompile.py --all. No public
signature or definition changed. The unit route remains unchanged.

## Proved and sorry left

- Closed the original hole `CategoryTheory.Functor.exactMateComparison_eq`
  (node `lem-pc-exact-left-adjoint-derived-mate-compatibility`) by decomposition.
- Proved the local equation `comparison_unit` directly from
  composition and natural-transformation factorization equations.
- Added one hole `CategoryTheory.Functor.derivedMate_pastedUnit`, in the new module
  `Sheaf.CategoryTheory.DerivedMatePastedUnit`, node `lem-pc-derived-mate-pasted-unit`.
  This is the only sorry in the delivery. Its docstring states its source and the
  componentwise proof, and its node records the calculation steps.

## No longer needed

None. The existing imports supply the statement/definition API or mates machinery and
remain required. Both original proof dependencies remain used. No unit node is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original DAG marked all normalization work elementary;
the pasted mate calculation is substantial enough to deserve a separate proof obligation.
The comparison factorization, K-injective preservation, right-derived uniqueness, and
inverse mate law are now written and checked in Lean.

Edge cases of the new helper were checked algebraically: zero natural transformations
make both sides zero; identity adjunctions give the original normalized-square equation
with exact factor isomorphisms; zero categories have unique morphisms. The argument never
cancels a noninvertible derived unit. For arbitrary squares, the factorization equations
and naturality provide precisely the required normalization.

## New nodes

`lem-pc-derived-mate-pasted-unit`: the forward mate of any normalized derived square has
the pasted unit of the localized ordinary mate. This is the calculation between the
proved comparison-unit normalization and the proved right-derived uniqueness step.
One new module, one public theorem with sorry; no change records or forced adaptations.

## Second reading by S1

1. Compared the complete existing module and existing node with the repository using
   diff. The only Lean changes are one plain proof-only import and the proof of
   `CategoryTheory.Functor.exactMateComparison_eq`; all existing declaration signatures,
   section variables, visibility, options, and the comparison definition are byte for
   byte unchanged. Existing node changes are restricted to proof, proof_deps, and
   proof_origin. No change record or forced adaptation is needed. Verdict: pass.
2. Compiled both modules in import order with lcompile.py --all: no errors or warnings.
   Scanned both sources: the sole sorry is the whole proof of the named public theorem
   `CategoryTheory.Functor.derivedMate_pastedUnit`; no forbidden declarations or hollow
   definitions. A scratch-copy axiom probe reports only propext, Classical.choice,
   Quot.sound for exactMateComparison; those three plus sorryAx for exactMateComparison_eq
   and derivedMate_pastedUnit. Verdict: valid reduction, with the reported open lemma;
   not an axiom-free proof of the original theorem yet.
3. Read the helper statement, docstring and node together, and checked the componentwise
   argument against mateEquiv, derivedη_fac_app and derivedε_fac_app in their source files.
   Naturality moves p and f through the derived mate; hβ replaces the middle square;
   the G-unit and H-counit equations reduce it to the localized ordinary mate. Only the
   exact localization factor isomorphisms are canceled. Identity adjunctions reduce to
   the given normalized square; zero squares give zero on both sides by additivity;
   zero categories give the unique morphism. The statement needs no invertibility of
   either square or preservation of K-injectives by H. It leaves out the particular
   comparison, its factorization proof, identification of the ordinary mate, and
   right-derived uniqueness, so it is a proper intermediate step, not a restatement.
   Repeated leanfinder, loogle and grep searches with different queries and searched both
   library roots with rg. The closest upstream theorem, derivedPlus_mateEquiv_app_fac,
   concerns bounded-below categories and exact vertical functors. It cannot be applied
   to the arbitrary F and K here. A short scratch proof attempt did not close the helper.
   Verdict: true, needed, and appropriately split off; one original hole closed and
   one new hole added, net zero.
4. Checked the comparison_unit calculation and the subsequent mate inverse laws and
   rightDerived_ext application. P's K-injective preservation follows from the exact
   left adjoint H. The pasted-unit lemma is the remaining calculation. All three original
   public imports occur in public signatures or the comparison definition; the new
   import is proof-only. The two original proof dependencies still occur in the written
   argument, so No longer needed = none is complete. Read
   dag/units/sk-thm-picard-semicon.json: no realized node or unit route is removed or
   changed; its existing empty realization fields are outside this delivery. Verdict: pass.
5. Checked the nodes' statements, Lean records, proof steps, dependency unions, source,
   origin and new-node fields against both modules. The main node now records comparison
   normalization, the helper application, and uniqueness/inverse-mate assembly. The
   helper has its matching theorem and blueprint tag, complete natural-language proof,
   creation record, inherited chapter/unit, and logged searches. Verdict: pass.

Changes by the second reader: corrected the helper docstring's P-image wording to
Q-image (the forward mate applies the right adjoint Q to the square at P(X)); expanded
its componentwise natural-language proof to identify every normalization and naturality
step; added the independent search results to the new node and this review to the report.
No Lean statement, definition, proof body, import, or proof dependency was changed.
