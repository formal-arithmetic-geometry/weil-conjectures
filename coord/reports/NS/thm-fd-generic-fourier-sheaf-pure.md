# Stage-1 report: thm-fd-generic-fourier-sheaf-pure

Files written:

- `dag/nodes/sec-deligne-laumon-a1/thm-fd-generic-fourier-sheaf-pure.json` — statement, no new nodes; Mathlib searches found no match (only generic analytic Fourier declarations).
- `dag/units/sk-p-dl-a1-some-weight.json` — realized statement and proof step for the key unit.
- `citations.json` — verbatim statement excerpts for every cited node in every proof step.

Attachments:

- No sorry-free slopmaster2 declaration attaches to this item. The declaration `AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner` in `WeilConjectures/DeligneLaumon/AffineLine/Purity.lean:44-50` is still proved by `sorry`.

WANTED:

- None. The proof route uses the existing DAG nodes and the main-20261015 blueprint; no external document had to be fetched.

What was wrong or changed:

- The imported item used the older master snapshot and omitted the explicit nontrivial additive character. I aligned its statement and source metadata with `literature/blueprint/main-20261015/.../thm-fd-generic-fourier-sheaf-pure.md`, whose target hypotheses match the upstream Lean declaration.
- The current statement quantifies over an arbitrary lisse Fourier partner, so its proof cannot assume partner irreducibility as an unstated hypothesis. I added the missing argument in Step 3: the source middle extension is simple, Fourier t-exactness is an exact equivalence, and the simple-object classification therefore makes the given partner a nonzero irreducible lisse sheaf. The existing `lem-wf-dense-open-pi1-surjective` then preserves irreducibility after restricting to the chosen dense open.
- The old Step 4 cited `lem-a1-constituent-nonexceptional-comparison` for a direct-image stalk assertion that this node does not state. I removed that citation and apply the consequence clause of `cor-wf-unramified-boundary-purity` directly.

What I could not finish:

- No Lean files were written and no compiler or Lake command was run, as required for this stage-1 run.

## Review by NS

I read the current item source in the main-20261015 blueprint, the archived master item, the upstream `Purity.lean` declaration, and the complete statements of every dependency used by the five proof steps. Step 1 uses the realified-kernel reality statement, the concentration/direct-summand clause, and realness of the degree-one pushforward; those statements provide exactly the reality and vanishing assertions used. Step 2 uses the zero-extension comparison for the shifted transform and its short exact sequence, while the middle-extension definition identifies `j'_* M'` with the required ordinary direct image. Step 3 uses generic lissity on a dense open, the simple-object classification, Fourier t-exactness and its quasi-inverse equivalence, and the existing dense-open restriction theorem; these supply respectively the lisse locus, partner nonzero irreducibility, transfer of simplicity, and preservation of irreducibility. Step 4 uses the pointwise definition of reality, the real-lisse purity theorem for irreducible constituents, and the determinantal-weight definition; the quotient from Step 3 makes the restricted partner a constituent. Step 5 uses precisely the consequence clause of the unramified-boundary purity corollary, with the lisse sheaf `M'` on `U'_0` and its pure restriction to `V'_0`.

I checked the hypotheses at each use: `M` is nonzero irreducible, constituent-nonexceptional, and pure; `ψ` is explicitly nontrivial; the zero-extension comparison has the finite-complement condition because a dense open of the affine line has finite complement; `V'_0` is a dense open in the smooth geometrically connected affine line; and all restrictions are within the lisse Weil category. I tested the edge cases of an empty missing set (`V'_0=U'_0`), a rank-one pure sheaf, and a zero boundary correction. The imported direct-image citation in the last step was removed because it did not state that fact. No duplicate or new statement node was introduced, and each entry in `citations.json` is a verbatim substring of the cited node statement.

The generic nodes `lem-wf-dense-open-pi1-surjective`, `thm-a1-fourier-t-exact`, and `prop-a1-curve-perverse-simples` are declared in `split_report.tool_uses` because they are black-box tools from neighboring units; they establish generic restriction and perverse-category facts rather than replacing the Fourier-weight route.
