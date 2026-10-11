## Worker report

Recorded an existing statement; no Lean module is written and no definition or proof is added.
The exact declaration is
`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`
in module `WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem`, source file
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`,
lines 168–172 (docstring starts at line 157). I read its whole signature and docstring,
as well as its proof and the upstream finite-approximation and immersion-descent statements.
Its proof uses a sorried finite-approximation theorem; this is an existing statement record,
not a claim that the theorem is established without sorry dependencies.

The recorded signature is verbatim:

```lean
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f]
    [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsFinite p ∧ j ≫ p = f
```

Clause-by-clause correspondence:

- Schemes X and S and morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Separated morphism: `[IsSeparated f]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`; together these are
  exactly finite type, not merely locally finite type.
- Everywhere quasi-finite: `[LocallyQuasiFinite f]` together with the finite-type
  hypotheses. Mathlib's locally quasi-finite condition does not on its own imply
  locally finite type, which is explicitly present here. Under these hypotheses
  it is equivalent to finite fibres by
  `AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`.
- S quasi-compact: `[CompactSpace S]`, meaning compactness without a Hausdorff condition.
- S quasi-separated: `[QuasiSeparatedSpace S]`, equivalent to compact intersections
  of affine opens by `AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens`.
- Existence of a scheme T: `∃ (T : Scheme.{u})`.
- The arrows j from X to T and p from T to S: `(j : X ⟶ T) (p : T ⟶ S)`.
- j a quasi-compact open immersion: `IsOpenImmersion j ∧ QuasiCompact j`.
- p finite: `IsFinite p` (the Mathlib affine and module-finite morphism property).
- Factorization f = p composed with j: `j ≫ p = f` with Lean's forward
  categorical composition; equality orientation changes no mathematical content.

The node has `stmt_deps: []`, so there are no dependency-node records to import or repair.
All notions in the signature are already defined in Mathlib. I read the definitions/docstrings
in `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` (LocallyQuasiFinite),
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (LocallyOfFiniteType),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (QuasiCompact),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (scheme quasi-separatedness), and
`Mathlib.AlgebraicGeometry.Morphisms.Finite` (IsFinite).

Source check: opened https://stacks.math.columbia.edu/tag/05K0, Lemma 37.43.3.
Its quasi-finite separated morphism over a qcqs base has the same factorization and
both stated properties of j. The node's explicit finite-type formulation is the
usual quasi-finite formulation of this lemma. No statement correction is needed.
The blueprint source file is not present in this read-only machine's literature tree;
the node records its full statement and proof, and the cited Stacks page was read.

Edge cases checked by reading the quantifiers and definitions: empty X and empty S are
not excluded (no Nonempty hypotheses); schemes need not be reduced, integral, affine,
Noetherian, or of finite presentation; no characteristic or base field is imposed.
For empty X one can take empty T; for an identity of a qcqs base one can take T = S
and both maps identities. The shared universe u is the usual Scheme universe and
permits arbitrary size by instantiation; there is no small test-object quantifier.
No hollow base conditions such as QuasiCompact of the identity occur.

Searches performed:

- `msearch.py ... leansearch "Zariski main theorem finite morphism open immersion factorization"`:
  service unavailable (Internal Server Error); recorded as unavailable, no verdict.
- `msearch.py ... leanfinder "A separated quasi-finite morphism of finite type to a
  quasi-compact quasi-separated scheme factors as an open immersion followed by a finite morphism"`:
  8 results on finite composition, immersions, locally quasi-finite and separatedness;
  no exact finite-factorization theorem in Mathlib.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsOpenImmersion"`:
  OK, 0 hits.
- `msearch.py ... grep "exists.*[Ff]inite|[Ff]inite.*factorization|exists_isOpenImmersion_comp_isFinite"
  AlgebraicGeometry`: 15 results, none the finite factorization; Mathlib's
  ZariskisMainTheorem gives an integral normalization factorization.
- `rg` over source WeilConjectures and project lean/Sheaf for Zariski, quasi-finite
  factorization, finite/open-immersion existence, and QuasiFinite: related results;
  no project duplicate.
- `rg -n "thm-pqf-zmt-factorization|exists_isOpenImmersion_comp_isFinite|
  exists_openImmersion_finite_factorization"` over source, project and
  `dag/lean_names_upstream.json`: found the source module's blueprint references.
  Opening the full module located the exact theorem above.
- `rg` of `dag/lean_names_upstream.json` for finite-factorization/existence names:
  the exact theorem is absent from the stored name list; the source text confirms it.

No new nodes, dependency modules, statement changes, or disputed statements.
The independent second reading is left to the second reader as instructed.

## Second reading by C1

I independently opened the node (including its four proof steps), the recorded upstream
module at lines 157–182, and the Mathlib declarations underlying the signature. The existing
record is correct: no Lean module, new definition node, dependency module, or statement
correction is needed. The recorded `lean.statement` was compared with the source substring
from `theorem` to `:= by` and is verbatim identical.

Source: I read Stacks Tag 05K0 (Lemma 37.43.3), and downloaded and read the actual
`more-morphisms.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
section `section-application-etale-neighbourhoods` and lemma
`lemma-quasi-finite-separated-pass-through-finite` (lines 12304–12325 and 12456–12505).
There are no standing field, Noetherian, reducedness, or finite-presentation assumptions in
that section. The lemma assumes quasi-finite and separated over a qcqs base and concludes
exactly the node's factorization. Its following addendum adds finite presentation; that is
not an assumption of this item. The node's explicit finite-type formulation is equivalent
to the source's quasi-finite formulation.

My object/hypothesis/conclusion checklist, in node order:

- Schemes X and S: `{X S : Scheme.{u}}`; verdict: same unrestricted scheme objects.
- Morphism f from X to S: `(f : X ⟶ S)`; verdict: same arrow, fixed before the witnesses.
- f separated: `[IsSeparated f]`; verdict: exact. I read `Morphisms/Separated.lean:44`,
  defining this by the closed-immersion diagonal.
- f of finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`; verdict: exact, not an
  additional assumption. I read `Morphisms/FiniteType.lean:43` (finite-type affine chart
  ring maps) and `Morphisms/QuasiCompact.lean:43` (compact inverse images of compact opens).
- f everywhere quasi-finite: `[LocallyQuasiFinite f]`; verdict: exact in conjunction
  with the preceding finite-type assumptions. I read `Morphisms/QuasiFinite.lean:71`
  and the equivalence `locallyQuasiFinite_iff_finite_preimage_singleton` at line 325,
  whose hypotheses are precisely `[LocallyOfFiniteType f] [QuasiCompact f]`.
  Thus the condition gives finite fibres everywhere; the separate finite-type binders
  are necessary because Mathlib's local quasi-finiteness alone omits finite type.
- S quasi-compact: `[CompactSpace S]`; verdict: exact topological quasi-compactness,
  with no Hausdorff or separation condition added.
- S quasi-separated: `[QuasiSeparatedSpace S]`; verdict: exact. I read
  `quasiSeparatedSpace_iff_forall_affineOpens` in `Morphisms/QuasiSeparated.lean:56`,
  expressing compact intersections of affine opens.
- A scheme T: `∃ (T : Scheme.{u})`; verdict: same existential scheme.
- An arrow j from X to T: `(j : X ⟶ T)`; verdict: same existential arrow.
- j an open immersion: `IsOpenImmersion j`; verdict: the standard Mathlib scheme
  open-immersion property (`OpenImmersion.lean:38`), not merely an injective map.
- j quasi-compact: `QuasiCompact j`; verdict: separately present, exact.
- An arrow p from T to S: `(p : T ⟶ S)`; verdict: same existential arrow.
- p finite: `IsFinite p`; verdict: exact. I read `Morphisms/Finite.lean:39`: affine
  inverse images and module-finite ring maps on every affine target open.
- f = p composed with j: `j ≫ p = f`; verdict: exact categorical composition,
  with the harmless reversed orientation of equality. All three witnesses precede
  the conjunction of their required properties; none is chosen independently of f.

There are no statement-dependency nodes (`stmt_deps` is empty), hence no dependency
signatures or new-node source checks are missing. All notions above are Mathlib notions;
no private definition is supplied. I also read the upstream proof: it takes the relative
normalization, obtains its finite approximation, descends the open immersion into a closed
subscheme of a stage, and composes that closed immersion with the finite stage map.
These are the node's four proof steps. The upstream docstring names Tag 05K0 and this
blueprint and explains this route. Existing-source records require no newly written
sorry-only proof or docstring; this delivery adds no proof or hollow definition. As the
worker already states, an upstream finite-approximation input is sorried, so this record
is not a claim of stage-3 completion.

Edge cases: X may be empty, and an arrow to empty S forces X empty; no Nonempty binder
excludes either. The identity of any qcqs scheme is covered. Nilpotents, disconnected
schemes and arbitrary characteristics are allowed; no field or Noetherian instance occurs.
There is no natural-number or index-set parameter, so n = 0 and empty indexing families
impose no additional case. The universe u is explicitly bound in the source module and
arbitrary; T can be constructed in the same scheme universe. There is no independently
smaller test-object universe. All variables in the recorded signature are bound.

Independent searches (using different wording from the first reader):

- `msearch.py ... leanfinder "A quasi-finite separated map of schemes admits a compact
  open embedding into a scheme finite over its qcqs target"`: eight hits on local
  quasi-finiteness and compactness, no full factorization.
- `msearch.py ... loogle "AlgebraicGeometry.LocallyQuasiFinite, AlgebraicGeometry.IsFinite"`:
  seven hits, including proper quasi-finite implies finite and finite fibres; none
  states the existential factorization.
- `msearch.py ... grep "finite factorization|finite-factorization|exists.*[Oo]pen.*[Ff]inite|[Ff]inite.*[Oo]pen.*[Ii]mmersion"
  AlgebraicGeometry`: nineteen related Mathlib hits, no full finite factorization.
- I ran `rg` with the finite-factorization/open-finite expressions over all upstream
  `WeilConjectures` and project `lean/Sheaf`. This independently found the recorded exact
  theorem and the upstream finite-presentation refinement. I opened the project's
  `QuasiFiniteAffineOpenInFinite.lean:46`: its theorem assumes affine X and Y and is
  only an affine special case, not this statement. The refinement adds finite
  presentation, also not this statement. The exact upstream name is absent from
  `dag/lean_names_upstream.json`; the directly opened source is authoritative here.

No mathematical or record mismatch was found, and no correct material was rewritten.
Second reading changed only this report by adding the independent source and signature
review. Since this is an existing declaration with no delivery modules, there is no new
Lean file to compile; the delivery tool checks the existing-record packet.
