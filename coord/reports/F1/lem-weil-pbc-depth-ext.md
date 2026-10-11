## Worker report

The module `Sheaf.RingTheory.DepthExt` states
`IsLocalRing.exists_depth_eq_ext_degree`, with its sole proof `sorry`.
The statement is precisely the characterization in Stacks, Algebra,
Lemma 10.72.5, Tag 00LW: https://stacks.math.columbia.edu/tag/00LW.
The local literature/stacks-project/algebra.tex is absent on this machine;
I opened the official tag, including its statement and induction proof.
No statement correction, dependency module, or new node is needed.

Hypotheses and clauses:

- A commutative ring R: `{R : Type u} [CommRing R]`.
- Noetherian: `[IsNoetherianRing R]`.
- Local with its unique maximal ideal m: `[IsLocalRing R]` and
  `IsLocalRing.maximalIdeal R`. The maximal ideal need not be separately chosen.
- An R-module M: `(M : Type v) [AddCommGroup M] [Module R M]`.
- Finite (finitely generated): `[Module.Finite R M]`.
- Nonzero: `[Nontrivial M]`, equivalent to a module not being the zero module.
- Residue field κ = R/m: `R ⧸ maximalIdeal R`, regarded as an R-module.
- The i-th Ext in the abelian category of R-modules:
  `CategoryTheory.Abelian.Ext (ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R)))
  (ModuleCat.of R (ULift.{u} M)) i`.
  The two carriers have independent universes u and v; ULift places them in
  max u v without imposing a Small assumption or an inequality on u and v.
  `ULift.moduleEquiv` is the canonical R-linear equivalence with the original
  carrier, so these are the same modules up to canonical isomorphism,
  not substituted algebraic objects or specialized modules. Mathlib's
  ModuleCat HasExt instance applies in this common universe.
- There exists a nonnegative integer with nonzero Ext: `∃ i : ℕ` and the
  `Nontrivial (Ext ... i)` conjunct. Ext is an abelian group, so Nontrivial
  is precisely nonzero and Subsingleton is precisely the zero group.
- Depth is finite and equals that degree: `depth (R := R) M = (i : ℕ∞)`.
  Being equal to a natural number already expresses finiteness.
- The degree is the smallest: `∀ j : ℕ, j < i → Subsingleton (Ext ... j)`.
  Together with nonzero Ext at i this is exactly minimality.

Dependency declarations, whose full definitions and docstrings were read:

- def-weil-pbc-noetherian-ring: `IsNoetherianRing`,
  Mathlib.RingTheory.Noetherian.Defs (all ideals finitely generated).
- def-weil-finitely-generated-module: its mathlib_match `Module.Finite`,
  Mathlib.RingTheory.Finiteness.Defs (top submodule finitely generated).
  This node has no lean record and needs none; its mathlib_match is usable.
- def-pc-ext: `CategoryTheory.Abelian.Ext`,
  Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic, the small model of
  derived shifted Hom; the ModuleCat instance is from
  Mathlib.Algebra.Category.ModuleCat.Ext.HasExt.
- def-weil-pbc-depth: `IsLocalRing.depth` and `Ideal.depth`,
  Sheaf.RingTheory.Depth. Depth is the recorded regular-sequence supremum
  with infinity for IM=M, not a new definition by Ext.

The declaration docstring carries every proof step of the node with its
supporting DAG identifiers: Nakayama and finite depth, the zeroth Ext and
associated-prime criterion, quotient by the first element of a maximal
regular sequence, the long exact Ext sequence with zero scalar maps, and
inductive vanishing and nonvanishing (including depth one).

Edge cases checked before writing: M=0 is explicitly excluded, as the node
requires (its depth is infinity and all Ext groups vanish). A zero ring is
excluded by the local-ring hypothesis. A field has maximal ideal zero and
nonzero Hom in degree zero, so i=0, with no smaller degrees to check. More
generally i=0 gives a vacuous vanishing clause. At depth one the docstring
explicitly uses Ext-zero vanishing to finish the inductive step. No
characteristic assumption, finite underlying-set assumption, or positive
ring-dimension assumption is added. Independent universes are covered by
canonical ULifts.

Searches made (all msearch calls are recorded in searches.jsonl):

- leanfinder: "depth of a finite module over a Noetherian local ring is the
  smallest degree of nonzero Ext from the residue field". Eight hits on
  support dimension and regular sequences; none states this theorem.
- loogle: "ModuleCat.exists_isRegular_tfae". One hit, Rees' theorem in
  Mathlib.RingTheory.Depth.Rees, relating Ext vanishing below a fixed n to
  regular sequences of length n. This does not assert finite depth or
  existence of a first nonzero Ext degree and is not the same statement.
- grep: "depth.*[Ee]xt|[Ee]xt.*depth" in Mathlib/RingTheory. Zero hits.
- leansearch: "depth equals least degree of nonzero Ext over a Noetherian
  local ring". Service unavailable (Internal Server Error); recorded as
  unavailable, without a verdict of absence.
- rg: "depth.*[Ee]xt|[Ee]xt.*depth|lem-weil-pbc-depth-ext" in
  WeilConjectures and lean/Sheaf. Only an unrelated depth-two discussion
  in EtaleTorsorSpreading.lean; no matching statement.
- rg for `exists_depth_eq_ext_degree` in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no existing declaration.

Server single-file compile: clean, 1.7 seconds, exit code 0. All variables
and universes are explicitly bound. No disputed statement was found.

## Second reading by F1

I read the node statement, Stacks Algebra Lemma 10.72.5 (Tag 00LW), and the
module independently. The source says: a Noetherian local commutative ring
`(R,m)` with its unique maximal ideal, a nonzero finite `R`-module `M`, the
residue field `kappa = R/m`, and the least nonnegative degree in which
`Ext_R^i(kappa,M)` is nonzero; it concludes that this degree exists and equals
`depth_m(M)`.

- `{R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]` gives the
  commutative Noetherian local ring, with `maximalIdeal R` supplying its unique
  maximal ideal.
- `(M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Nontrivial M]` gives exactly a finite nonzero R-module.
- `R ⧸ maximalIdeal R`, lifted by `ULift.{v}`, is the residue field as an
  R-module. The second argument is `ULift.{u} M`; both carriers lie in the
  common module-category universe without imposing an inequality on `u` and
  `v`.
- `Ext (ModuleCat.of R (ULift.{v} (R ⧸ maximalIdeal R)))
  (ModuleCat.of R (ULift.{u} M)) i` is Mathlib's abelian-category Ext for
  R-modules. `∃ i : ℕ` gives existence, `Nontrivial (...)` gives nonzero Ext,
  `depth (R := R) M = (i : ℕ∞)` gives the finite depth equality, and
  `∀ j : ℕ, j < i → Subsingleton (...)` gives vanishing in every smaller
  degree, hence leastness. The conjunction order preserves all clauses.

No mismatch was found and no source or Lean text was changed. The source does
not assume a characteristic, positive dimension, finite ring, or nonzero depth;
the Lean adds none. The empty lower-degree range when `i = 0` is handled by the
vacuous universal clause. The zero module is excluded by `Nontrivial M`, as in
the source. A field has maximal ideal zero and is covered with `i = 0`. The
zero ring is excluded by `[IsLocalRing R]`, whose Mathlib definition includes
`Nontrivial R`. Independent universes are covered by the two explicit ULifts.

I checked the dependency declarations: `IsNoetherianRing` and `Module.Finite`
are the recorded Mathlib notions, `CategoryTheory.Abelian.Ext` is the recorded
Mathlib Ext definition (with the ModuleCat HasExt instance), and
`IsLocalRing.depth` is the project definition in `Sheaf.RingTheory.Depth`.
None is a private duplicate or a special-case replacement. Searches over
Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream-name index found no
existing `exists_depth_eq_ext_degree`; Mathlib's `ModuleCat.exists_isRegular_tfae`
is only a regular-sequence/Ext vanishing equivalence and does not state this
finite-depth least-degree theorem. The module compiles cleanly with the remote
single-file compiler.
