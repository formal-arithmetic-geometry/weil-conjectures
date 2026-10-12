## What changed

Corrected AlgebraicGeometry.proper_limit_noetherian_affine_clause in
Sheaf.AlgebraicGeometry.ProperLimitNoetherianCore: it constructs an affine-base
system instead of asserting properties of every supplied system. The corrected
construction has a complete Lean proof using affine Noetherian approximation,
proper descent, closed images, directed reindexing, finite-type affine-open
sections, and preservation of affine limits by global sections.

Adapted only the proof of AlgebraicGeometry.exists_proper_limit_noetherian in
Sheaf.AlgebraicGeometry.ProperLimitNoetherian. Its signature, visibility and
imports are unchanged. Updated the affine-clause DAG statement and proof route.
The core theorem and its DAG route are unchanged; a stale sandbox node claiming
an unused alternative envelope route was restored to the repository version.

Change record: coord/changes/proper-limit-noetherian-affine-clause.md.

## Proved and sorry left

The baseline contains one sorry, in
AlgebraicGeometry.proper_limit_noetherian_affine_clause
(node lem-weil-pbc-proper-limit-noetherian-affine-clause).
Its old statement is false. This delivery corrects that statement and proves the
corrected existential construction; it does not prove the old assertion and
must not be counted as closing an unchanged theorem's hole.

AlgebraicGeometry.exists_proper_limit_noetherian_core
(node lem-weil-pbc-proper-limit-noetherian-core) was already proved and is unchanged.
There is no sorry in either delivered module, and no hole is added or split off.
The adapted caller AlgebraicGeometry.exists_proper_limit_noetherian was already
proved from the old affine clause and is now proved from the corrected one.
The compilation and axiom checks do not establish closure of all imported proofs.

## No longer needed

None. No import is removed and no global-closure pruning is claimed. The core
construction still uses the envelope clause of the existing combined theorem.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old affine clause asserted affine finite-type stages for
an arbitrary system with affine limit. Take X = S = Spec Q, f = id, and a constant
singleton system. Its cones are limits and f is proper, but Q is not finite type
over Z: finitely many generators invert only finitely many primes. Thus the old
assertion cannot be proved. The corrected existential chooses an affine
approximation before descending the proper envelope and forming closed images.
No target signature or definition changes.

The earlier reported delivery-tool blockers no longer occur: the current
--no-push dry run passes with CODEX review, including the forced adaptation.
No tools were modified and nothing was pushed. The earlier second-reader text
below is retained from the existing sandbox; this worker adds no second reading.

## Forced adaptations

Sheaf.AlgebraicGeometry.ProperLimitNoetherian is unclaimed in the current checkout.
The original compiles against the baseline (checked by deliver3.py), but fails
against the delivered core at its original line 86:

```
error: Function expected at
  proper_limit_noetherian_affine_clause f hS
Note: Expected a function because this term is being applied to the argument
  Λ
```

The corrected clause returns an existential construction and no longer accepts
an arbitrary previously chosen system. The caller's proof therefore branches on
IsAffine S before selecting a system: in the affine case it uses the corrected
construction and packages its affine clauses; otherwise it uses the unchanged
core construction and discharges the affine implication by contradiction. Only
the proof body (original lines 80--86) changes. Every existing signature and
visibility, and every import, stays identical. Both adapted modules compile
without errors or warnings using lcompile.py --all.

## Earlier second reading (a previous round; superseded)

1. **Repository visibility:** Compared the delivered core module with the repository version. The core theorem statement is unchanged; the affine clause has the declared statement correction and its change record. The adapted caller keeps its public statement byte for byte unchanged.
2. **Compilation and axioms:** Compiled both delivered modules with `lcompile.py --all`; both compile without errors. The core proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The axiom probes retain sorryAx from imported dependencies; this delivery does not close those imported proofs.
3. **Statements and dependencies:** The corrected affine construction is true and matches the Stacks Tag 0A0P route: it constructs the affine system before proving affine finite-type stages and the global-sections colimit. Its DAG node and proof dependencies agree with the proof. No duplicate library statement was introduced.
4. **Pruning and route:** The unit route is preserved: envelope, affine Noetherian approximation, proper descent, closed images, directed reindexing, and affine global sections. No unused import or proof dependency was found. The adapted caller now branches on `IsAffine S`, selecting the corrected construction in the affine case and the core construction otherwise.
5. **Changes made:** Added the adapted `ProperLimitNoetherian` module to the sandbox and replaced its obsolete application of the old affine-clause signature with the corrected existential construction. No new theorem or sorry was added.


## Second reading by T2

1. **Visibility and signatures — pass.** Independently diffed both delivered modules
   against the repository. The core declaration and its entire proof are unchanged.
   The only signature change is the affine clause, explicitly declared in the report,
   change record, and node statement_change. The caller's signature, visibility, and
   imports are byte-for-byte unchanged; its proof changes only to select the affine
   construction before choosing an inverse system. No definition or target changes.
2. **Proof and axioms — pass with inherited holes.** Independently compiled both
   modules using lcompile.py --all, without errors or warnings. Searched the delivered
   Lean for sorry, axiom, unsafe, opaque, implemented_by, and extern: none occur.
   Scratch-copy #print axioms checks of exists_proper_limit_noetherian_core,
   proper_limit_noetherian_affine_clause, and exists_proper_limit_noetherian each
   report exactly propext, Classical.choice, Quot.sound, and inherited sorryAx.
   There is no data definition introduced, and no arbitrary witness of an unproved
   existence theorem is installed as a definition. The existential choices occur
   inside proofs of propositions. Removed the scratch copies after verification.
3. **Statements and shortest routes — pass.** No theorem is split off or added.
   Checked the old clause on the singleton constant system X = S = Spec Q, f = id:
   all old hypotheses hold, whereas its finite-type conclusion fails. The corrected
   clause is the affine special case of the caller, with the needed construction
   and all its structural conclusions. Checked the construction of ofIsAffine:
   it uses actual finitely generated Z-subalgebras, including for the zero ring;
   thus empty affine schemes require no excluded hypothesis. Reviewed the proper
   envelope, proper-stage descent, closed-image system, and the initial reindexing
   applications. Searches with grep, leanfinder, and loogle plus rg over lean found
   no replacement theorem for this construction (loogle's IsProper query was not
   recognized). Mathlib's affine-preservation and finite-type lemmas are already
   used for the final clauses. Read the local Stacks limits.tex lemma corresponding
   to Tag 0A0P; the single-envelope/closed-image variant follows the existing core
   route rather than reproducing its double-index argument.
4. **Pruning and unit route — pass.** Every core import supplies public signature
   vocabulary or proof declarations/instances. There are no removed dependencies
   from the old core proof_deps; the old affine proof_deps was empty. No pruning is
   claimed. Read dag/units/sk-thm-p1.json: neither delivered intermediate realizes
   a unit-level step, and the realized route is unchanged. Retained the existing
   envelope, Noetherian approximation, descent, closed-image and directed-index
   route. The adapted caller is restricted to the forced proof change.
5. **DAG agreement — pass after metadata repair.** Checked both node files against
   their Lean declarations and proof applications. The core node is identical to
   the repository. The affine node states the corrected existential verbatim up
   to whitespace and records the actual six proof stages and their dependencies.
   Its statement_change includes the old statement and the sole caller. Corrected
   its group attribution from S2 to T2, retaining the schema-required stage 2
   label for statement changes; no mathematical DAG field needed
   further repair.

Second reading changed only the report (this independent review and the inherited
axiom clarification) and the statement-change attribution. No Lean proof or import
needed repair. One false holed signature is replaced by a proved corrected clause;
zero unchanged baseline theorem holes are closed, zero holes are added, and zero
statements are split off. This is a statement correction, not a proof of the old
false assertion and not an axiom-free closure of the imported development.


The first dry run rejected statement_change.by = "T2 stage 3": the static schema
requires "<G> stage 2" even for a stage-3 statement correction. Set the field to
"T2 stage 2" to identify the delivering group under that schema. The work and this
review remain stage 3. No delivery tool was changed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ProperLimitNoetherian
Original against changed dependencies failed:
```
/tmp/forced-adaptation-ni4x_rbm/lean/Sheaf/AlgebraicGeometry/ProperLimitNoetherian.lean:86:8: error: Function expected at
  proper_limit_noetherian_affine_clause f hS
but this term has type
  ∃ Λ x,
    ∃ (_ : Nonempty Λ) (_ : IsDirected Λ fun x1 x2 ↦ x1 ≤ x2),
      ∃ Xs Ss fs πX πS,
        Nonempty (IsLimit { pt := X, π := πX }) ∧
          Nonempty (IsLimit { pt := S, π := πS }) ∧
            (∀ (i j : Λᵒᵖ) (a : i ⟶ j), IsAffineHom (Xs.map a) ∧ IsAffineHom (Ss.map a)) ∧
              (∀ (i : Λᵒᵖ), IsProper (fs.app i)) ∧
                (∀ (i : Λᵒᵖ),
                    LocallyOfFiniteType (specULiftZIsTerminal.from (Ss.obj i)) ∧
                      QuasiCompact (specULiftZIsTerminal.from (Ss.obj i))) ∧
                  (∀ (i : Λᵒᵖ), πX.app i ≫ fs.app i = f ≫ πS.app i) ∧
                    (∀ (i : Λᵒᵖ),
                        IsAffine (Ss.obj i) ∧ (algebraMap ℤ ↑(Scheme.Γ.obj (Opposite.op (Ss.obj i)))).FiniteType) ∧
                      Nonempty (IsColimit (Scheme.Γ.mapCocone { pt := S, π := πS }.op))

Note: Expected a function because this term is being applied to the argument
  Λ

(with the modules compiled into /tmp/forced-adaptation-ni4x_rbm/.lbuild) [6.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
