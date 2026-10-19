## Worker report

The module `Sheaf.RingTheory.AuslanderBuchsbaum` states
`IsLocalRing.depth_eq_projectiveDimension_add_depth`, with `sorry` as its only proof.
No definitions, dependency modules, new nodes, or statement corrections are needed.
Source read: Stacks Project, algebra.tex, proposition-Auslander-Buchsbaum (Tag 090V),
including its proof. The declaration docstring carries all nine steps of the DAG proof,
with their dependency IDs. All recorded proof-dependency modules are imported; Mathlib
leaves are imported through their source modules.

Hypothesis and clause correspondence:

- Commutative ring R: `{R : Type u} [CommRing R]`.
- Noetherian: `[IsNoetherianRing R]`.
- Local with its unique maximal ideal: `[IsLocalRing R]`; the recorded
  `IsLocalRing.depth` uses `IsLocalRing.maximalIdeal R`.
- An R-module M: `(M : Type v) [AddCommGroup M] [Module R M]`.
- Nonzero M: `[Nontrivial M]`.
- Finitely generated M: `[Module.Finite R M]`.
- Finite projective dimension: the explicit proof
  `h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)`.
- Depth of R: `depth (R := R) R`, using its self-module structure.
- Projective dimension of M: `ModuleCat.projectiveDimension (ModuleCat.of R M) h`,
  the least length of a bounded projective resolution, coerced from natural numbers
  into `ℕ∞` to add depths.
- Depth of M: `depth (R := R) M`.
- The entire conclusion is the equality of the first depth with that sum; no
  finiteness-of-depth hypothesis, extra conclusion, or bound is introduced.

Statement dependency declarations (their full signatures and docstrings were read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, whose ideals are finitely
  generated (`isNoetherianRing_iff_ideal_fg`).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, generated top submodule.
- `Sheaf.RingTheory.GlobalDimension`: `ModuleCat.HasFiniteProjectiveDimension`,
  `ModuleCat.HasProjectiveResolutionLE`, and `ModuleCat.projectiveDimension`.
- `Sheaf.RingTheory.Depth`: `Ideal.depth` and `IsLocalRing.depth`; the former is
  the regular-sequence length supremum with the specified infinity convention,
  and the latter specializes it to the maximal ideal.

Edge cases checked: nontrivial M excludes the zero module precisely as in the node.
It also rules out a zero coefficient ring. Projective dimension zero is allowed,
including a nonzero finite free module, and the formula then equates its depth with
that of R. Fields and depth-zero local rings are included. Depths retain their full
`ℕ∞` codomain; no unnecessary finite-dimension assumption is made. R and M have
independent, explicitly bound universes u and v, with no size restriction added.
There are no implicit auto-bound variables, local notation, or local instances.

Searches made:

- `msearch.py leanfinder`: "Auslander Buchsbaum formula depth of a Noetherian local
  ring equals projective dimension plus depth of a finite nonzero module" returned
  eight support/Krull-dimension results, including
  `Module.supportDim_add_length_eq_supportDim_of_isRegular`; none states this formula.
- `msearch.py loogle`: `"Auslander"` returned zero hits.
- `msearch.py grep`: `Auslander|Buchsbaum|depth.*projective|projective.*depth`
  returned zero Mathlib hits.
- `rg` in the upstream `WeilConjectures` tree for Auslander/Buchsbaum found the
  regular-local-ring UFD theorem and its scheme version, not this depth formula.
- `rg` in project `lean/Sheaf` found only related last-minors, residue-field-bound,
  and well-ordered-union modules, not the formula. The item ID has no upstream match.
- `rg` for `depth_eq_projectiveDimension_add_depth` in Mathlib, upstream source,
  project modules, and `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py NR lem-weil-pbc-auslander-buchsbaum` compiled the delivered
file cleanly on the server in 1.2 seconds (nice 19, two threads, 60-second limit).
Only the expected theorem `sorry` is present. No local compiler or build was run.
No statement dispute or dependency fault was found.


## Second reading by NR

I independently read the item node and the delivered module together with Stacks
`algebra.tex`, conventions, proposition-Auslander-Buchsbaum (Tag 090V), and its
entire proof. The source assumes commutative unital rings and states precisely the
node's formula for a nonzero finite module over a Noetherian local ring. It adds
no characteristic, residue-field, regularity, dimension, or completeness hypothesis.
No statement correction is necessary.

Object, hypothesis, and conclusion checklist, in the node's order:

- Ring R: `{R : Type u} [CommRing R]`. Same commutative unital ring; passes.
- Noetherian R: `[IsNoetherianRing R]`. I opened the recorded Mathlib
  `RingTheory.Noetherian.Defs`: this abbreviates `IsNoetherian R R`, whose
  field says every R-submodule of R is finitely generated. These are the ideals
  in the node; passes.
- Local R and its unique maximal ideal m: `[IsLocalRing R]`. I read the
  Mathlib local-ring class (including its nontriviality requirement) and the
  recorded `IsLocalRing.depth`. The latter explicitly uses `maximalIdeal R`;
  no arbitrary ideal is substituted. Passes.
- Module M: `(M : Type v) [AddCommGroup M] [Module R M]`. It is the full
  R-module notion, with an independent universe; passes.
- Nonzero M: `[Nontrivial M]`. For an additive group this is exactly M nonzero;
  passes.
- Finitely generated M: `[Module.Finite R M]`. I opened the recorded
  `Mathlib.RingTheory.Finiteness.Defs`: the field is `(top : Submodule R M).FG`,
  not finiteness of the underlying set or freeness. Passes.
- Finite projective dimension: `(h : ModuleCat.HasFiniteProjectiveDimension
  (ModuleCat.of R M))`. I opened the dependency node and its recorded module
  `Sheaf.RingTheory.GlobalDimension`: this is existence of n and a projective
  resolution zero above n, with no finite-global-dimension assumption on R.
  I also read Mathlib's `ProjectiveResolution` fields: a chain complex of
  projective modules and an augmentation quasi-isomorphism to M in degree zero.
  Thus the resolution is the augmented exact resolution of the node; passes.
- Depth of R: `depth (R := R) R`, in namespace `IsLocalRing`, uses R as its
  self-module and the unique maximal ideal. Passes.
- Projective dimension of M: `ModuleCat.projectiveDimension (ModuleCat.of R M) h`.
  Its dependency definition is `Nat.find h`, the least resolution length, not
  a selected upper bound. The cast to `ℕ∞` preserves this integer; passes.
- Depth of M: `depth (R := R) M`. I opened the depth dependency node and both
  definitions in `Sheaf.RingTheory.Depth`: maximal-ideal specialization of the
  supremum of lengths of `RingTheory.Sequence.IsRegular` lists, with infinity
  when IM = M. I also opened Mathlib's regular-sequence structure: injectivity
  modulo each prefix and nonzero final quotient. This matches the node and
  Stacks definition-depth. Passes.
- Entire conclusion: `depth (R := R) R =
  (ModuleCat.projectiveDimension (ModuleCat.of R M) h : ℕ∞) + depth (R := R) M`.
  It is exactly depth(R) = pd_R(M) + depth(M), with every clause and no additional
  bound, existential replacement, or finiteness hypothesis. Quantification is
  over R and M with the hypotheses before the conclusion; passes.

Edge cases: the zero module is excluded exactly by the source; the zero ring is
excluded by locality (and cannot support a nonzero unital module). Projective
resolution length zero is included and gives depth(R) = depth(M), including
nonzero finite free modules. Fields, depth-zero rings, and every characteristic
are included. Empty regular sequences contribute length zero, as required;
there is no index family or scheme, so empty index sets and empty schemes impose
no additional condition. Both depths retain their infinity convention without
assuming finite depth. Universes u and v are explicitly bound and independent;
no field or universe equality is introduced. No unbound variable remains.

Independent searches, using queries different from the worker's:

- `msearch.py leanfinder`: "For a finite module over a local ring the sum of its
  homological projective dimension and maximal regular sequence length equals
  ring depth". Eight hits concern support/Krull dimension and regular sequences,
  not the depth/projective-dimension formula.
- `msearch.py loogle`: `"projectiveDimension", "depth"`. Zero hits.
- `msearch.py grep`, RingTheory: `depth.*[+] |[+] .*depth|depth_eq|depth.*[Dd]imension|[Dd]imension.*depth`.
  Zero hits.
- Independent `rg` over the upstream `WeilConjectures` and project `lean/Sheaf`
  trees for depth/projective combinations, Auslander, Buchsbaum, and homological
  dimension/depth found related results only. I opened upstream
  `ModuleCat.free_of_hasProjectiveDimensionLE_of_annihilator`: it assumes an
  annihilator of the maximal ideal and concludes freeness, so it is a special
  depth-zero result, not this formula. The other Auslander–Buchsbaum theorem
  there concerns unique factorization. The project's residue-field depth bound
  is an inequality for the residue field, not this general equality.
- The full new declaration name has no entry in `dag/lean_names_upstream.json`.
  There is no existing exact statement requiring dropping this module.

There are no new nodes, dependency modules, private copies, or definitions in
this delivery. The existing dependency interfaces are usable. I checked the
module and theorem source/blueprint docstrings, all nine numbered proof steps
against the node, the proof-dependency imports, namespace, explicit universes,
100-character line limit, and the single whole-proof `sorry`. The node's
`lean.statement` is verbatim equal to the file signature (checked mechanically).
No H3–H9 mismatch was found; I left the correct Lean and node unchanged. The
second reading adds this report and independent search evidence only.

Validation: the delivered file was independently recompiled with
`scompile.py NR lem-weil-pbc-auslander-buchsbaum` on the server: 1.2 seconds,
nice 19, two threads, 60-second per-file limit; exit 0 and no warnings or errors.
No local compiler or global build was used.
