## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization` states
`AlgebraicGeometry.Scheme.Hom.exists_qcqs_finitePresentation_factorization` with proof
`sorry`. No definition, new node, dependency module, or statement correction is needed.
The original node is unchanged except for `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`, labels
`lemma-quasi-finite-separated-pass-through-finite` (Tag 05K0) and
`lemma-quasi-finite-separated-pass-through-finite-addendum` (Tag 0F2N), including both
proofs. The latter adds local finite presentation to the former's hypotheses and
makes the finite factor finitely presented. A finite morphism over a qcqs base has
qcqs source, giving precisely the node's final assertion.

Hypotheses and clauses, in order:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`, with explicit arbitrary universe `u`.
- Separated: `[IsSeparated f]`.
- Quasi-finite: `(hq : f.IsQuasiFinite)`, the recorded Stacks predicate, rather than
  Mathlib's weaker `LocallyQuasiFinite`. Its definition is locally of finite type,
  quasi-compact, and each singleton `{f.asFiber x}` open in `f.fiber (f x)`.
- The base is quasi-compact and quasi-separated: `[CompactSpace S] [QuasiSeparatedSpace S]`.
- Finite presentation of `f`: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, exactly the three conditions fixed by the conventions node.
  Some conditions follow from other hypotheses, but retaining these records precisely
  matches the node's explicit assumptions; none is an assumption true for arbitrary `f`.
- The factor and its arrows: `∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S)`.
- Quasi-compact open immersion: `IsOpenImmersion j ∧ QuasiCompact j`.
- Finite: `IsFinite p`.
- Finite presentation of `p`: `LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
  QuasiSeparated p`.
- Factorization: `j ≫ p = f`, Mathlib composition order for `f = p ∘ j`.
- Quasi-compact and quasi-separated intermediate scheme: `CompactSpace T ∧
  QuasiSeparatedSpace T`, explicitly in the existential conclusion.

Recorded statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`: `Scheme.Hom.IsQuasiFinite`.
  The complete module and its four predicates were read, including docstrings.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, from `def-sbc-locally-finite-presentation`'s
  `mathlib_match` (the node needs no `lean` record).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `def-weil-pbc-scheme-conventions` intentionally has no declaration: its record is a
  convention collecting the existing predicates. The relevant classes read are
  `QuasiCompact` (preimages of compact opens), `QuasiSeparated` (quasi-compact diagonal),
  and `IsSeparated` (closed-immersion diagonal), and scheme topological qcqs classes.
  No replacement convention definition is introduced.

Proof dependency imports: the recorded Zariski-main factorization module
`WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization` is imported
non-publicly, as is `Mathlib.AlgebraicGeometry.AffineTransitionLimit` for the recorded
open-descent lemmas. The remaining Mathlib proof tools are available through these
and the public imports. The two unstated proof nodes
`lem-weil-pbc-finite-closed-fp-approximation` and
`lem-weil-pbc-closed-limit-lfp-stabilization` have no module to import yet. Their steps,
and all six steps of the node, are carried in the theorem docstring, following the
node's route (finite approximation, descent of the open, closed-limit stabilization).

Edge cases checked: empty `X` is allowed (empty open immersion into the empty finite
scheme); empty `S` forces empty `X` and also presents no obstruction. Identity maps
of qcqs schemes admit the identity factorization. No nonempty, Noetherian, reduced,
affine, field, or characteristic assumption is imposed. Non-Noetherian bases are
included: finite does not by itself imply finite presentation, which is why local
finite presentation of `p` remains an explicit conclusion. The arbitrary scheme
universe includes every size of schemes in the node. No disputed statement was found.

Searches performed with `msearch.py NF lem-weil-pbc-quasifinite-fp-finite-factorization`:

- `leanfinder`: "A separated quasi finite finitely presented scheme morphism factors as
  a quasi compact open immersion followed by a finite finitely presented morphism with
  quasi compact quasi separated intermediate scheme". Eight hits, including
  `IsFinite.of_comp`, `IsImmersion.isImmersion_iff_exists_of_quasiCompact`,
  `LocallyOfFinitePresentation`, `IsSeparated.instQuasiSeparated`, and
  `QuasiCompact.of_comp`; no exact factorization theorem.
- `loogle`: `"LocallyQuasiFinite", "IsFinite"`. Seven hits on finite fibres, finite
  morphisms over Artinian bases and proper quasi-finite morphisms; no exact statement.
- `leansearch`: "finite presentation Zariski main factorization scheme". Service
  unavailable with Internal Server Error; not evidence of no match.
- `grep`: `exists.*isOpenImmersion.*isFinite|quasiFinite.*factor|zariski.*main`.
  Twenty-four Mathlib hits, on the algebraic and scheme Zariski main theorems,
  but none stating the finite finitely presented factor with explicit qcqs conclusion.
- `rg` of the source checkout and `lean/Sheaf` for factorization declarations and
  `quasifinite-fp-finite-factorization`: the existing upstream candidate
  `Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation`
  was read in full at lines 107–151 of `QuasiFiniteFactorization.lean`. Its conclusion
  omits `CompactSpace T`, `QuasiSeparatedSpace T` and the explicit quasi-compact and
  quasi-separated conditions on `p`; its hypothesis uses `LocallyQuasiFinite`.
  It is mathematical input for this statement, not the verbatim declaration required
  by this node (the node's `lean_candidates` already explains the qcqs omission).
  The affine-base sibling `QuasiFiniteAffineOpenInFinite` is a different statement.
- `rg` of Mathlib, upstream, project Lean, and `dag/lean_names_upstream.json` for
  `exists_qcqs_finitePresentation_factorization`: no name collision.

Validation: server-only `scompile.py` compiled the delivered module cleanly in 1.4 s,
nice 19, two threads, 60 s limit; no errors or unexpected warnings. No local Lean or
library build was run. The dry-run delivery result is recorded below after execution.


## Second reading by NF

Independent second reader: read the item node, its six proof steps, every statement
 dependency node and recorded declaration, the delivered module, and Stacks
`more-morphisms.tex` lines 12304–12327 and 12456–12530. The section introduces
no standing base, Noetherian, or characteristic hypothesis. Tag 05K0 assumes
quasi-finite and separated over qcqs S; Tag 0F2N adds local finite presentation.
The node expresses this as finite presentation of f: its extra quasi-compactness
already follows from its quasi-finiteness and its quasi-separatedness from
separatedness, so this is equivalent to the source, including over non-Noetherian S.
No statement correction or new/dependency module is necessary.

Object/hypothesis/conclusion checklist, in the node's order:

- Arbitrary schemes X and S and their map f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Pass: Mathlib schemes and their actual morphisms, arbitrary declared universe u.
- Separated f: `[IsSeparated f]`. Pass: Mathlib's closed-immersion diagonal.
- Quasi-finite f: `(hq : f.IsQuasiFinite)`. Pass: the recorded
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` definition gives local finite type,
  quasi-compactness, and isolation of every point in its scheme-theoretic fibre.
  Read all four signatures in that dependency module; the chosen predicate is
  precisely clause (3) of `pqf-def-quasifinite`, not just finite fibres.
- Quasi-compact and quasi-separated S: `[CompactSpace S] [QuasiSeparatedSpace S]`.
  Pass: topological quasi-compactness and compact intersections of affine opens;
  CompactSpace does not impose Hausdorffness.
- Finite presentation of f: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`. Pass: exactly the three-part convention. Read the Mathlib
  affine-chart ring-map definition, the preimages-of-compact-opens class, and the
  quasi-compact-diagonal class, and the convention node's record. No stronger
  finite-type, affine, or Noetherian assumption is hidden here.
- One intermediate scheme and two arrows: `∃ (T : Scheme.{u}) (j : X ⟶ T)
  (p : T ⟶ S)`. Pass: these witnesses occur after all hypotheses and share X and S.
- Quasi-compact open immersion j: `IsOpenImmersion j ∧ QuasiCompact j`.
  Pass: Mathlib's open immersion of locally ringed spaces, the recorded dependency.
- Finite p: `IsFinite p`. Pass: read Finite.lean's class extending IsAffineHom
  with finite ring maps on each affine open, exactly the finite-morphism node.
- Finite presentation of the same p: `LocallyOfFinitePresentation p ∧ QuasiCompact p
  ∧ QuasiSeparated p`. Pass: the identical three-part convention used for f.
- Factorization: `j ≫ p = f`. Pass: this is precisely f = p composed with j.
- Quasi-compact and quasi-separated T: `CompactSpace T ∧ QuasiSeparatedSpace T`.
  Pass: explicit properties of the same existential T, as required by the node.
  They follow from finiteness over qcqs S in the source situation.

Edge cases: empty X permits empty T; empty S forces empty X. Identity maps of
qcqs schemes allow identity witnesses. There is no nonempty binder, field,
characteristic, dimension, Noetherianity, reducedness, or affineness restriction.
There are no indices or natural-number parameters whose zero/empty cases need
separate exclusions. The common arbitrary universe u is the standard scheme
category universe, and imposes no test-object universe restriction. All variables
and universes are explicitly bound; signature checked byte-for-byte against
`lean.statement` and all Lean lines are at most 100 characters.

Independent duplicate searches (2026-10-15):

- LeanFinder via msearch: `Zariski Main Theorem finite presentation finite
  factorization over a quasi compact quasi separated base`: eight ring-theoretic
  quasi-finiteness results, no exact scheme factorization statement.
- Loogle via msearch: `"IsOpenImmersion", "LocallyOfFinitePresentation"`: only
  `locallyOfFinitePresentation_of_isOpenImmersion`, not this statement.
- LeanSearch via msearch: `A finitely presented separated quasi finite map factors
  through a finite finitely presented map with a quasi compact open immersion`:
  unavailable (Internal Server Error); no absence claim rests on it.
- rg across Mathlib algebraic geometry, all upstream WeilConjectures, and project
  lean/Sheaf for `exists.*[Ff]inite.*[Ff]actor`,
  `exists_isOpenImmersion_isFinite`, `qcqs_finitePresentation_factorization`, and
  `finitely presented.*factor`: inspected the upstream QuasiFiniteFactorization
  file in full, especially lines 121–151. Its refinement uses LocallyQuasiFinite
  and omits the node's explicit qcqs conclusion and the two global finite
  presentation conjuncts on p. It supplies input, not the full recorded signature.
  Also read project QuasiFiniteAffineOpenInFinite: affine-only, no fp refinement.
  No exact existing declaration and no collision of the new name was found.

H5/H6/H8/H9: the only declaration is the named theorem, its only proof is sorry;
there are no data definitions, private copies, local notation, or local instances.
The module and declaration source docstrings identify Tag 0F2N and this blueprint
node; the six-step proof plan follows all six node steps, including closed finite
fp approximation, open descent and eventual stabilization. The stated proof
modules are imported non-publicly; the two still-unstated auxiliary proof nodes
have no modules to import. No new node or dependency module needs an H12/H13 audit.

Mismatches found: none. Changed only this report by appending the independent
reading; kept the correct module and node unchanged. Server scompile validation
and the dry run/delivery follow this reading, with the required 60-second limit,
two threads and nice 19; no local compiler or library build is used.
