## Worker report

The module `Sheaf.AlgebraicGeometry.AffineCapSectionOpenAlgebra` states
`AlgebraicGeometry.affine_cap_section_open_algebra`, with its only proof `sorry`.
The node is unchanged except for `lean`; no new nodes or dependency modules are needed.

Read the algebra argument of Stacks Project Tag 01PV, Properties,
`properties-lemma-affine-cap-s-open`, at https://stacks.math.columbia.edu/tag/01PV
(the local literature checkout is absent). It explicitly constructs the symmetric algebra,
quotient by `s-1`, and identifies its spectrum with the indicated open subscheme.
The declaration docstring carries all four of the node's proof steps and their dependencies.

Hypothesis and clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- An R-module N: `(N : Type v) [AddCommGroup N] [Module R N]`.
- Invertible, explicitly defined by the node as finite projective of rank one:
  `[Module.Finite R N] [Module.Projective R N]` and
  `(_hN : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = 1)`.
  Rank is local rank, not a global free-module rank. Finite projective modules are locally
  free, and local rank one gives exactly the stated invertibility assumption.
- An element s of N: `(s : N)`.
- A = Sym_R(N) and its canonical inclusion: `SymmetricAlgebra R N` and
  `SymmetricAlgebra.ι R N s`.
- B = A/(ι(s)-1)A: `SymmetricAlgebra R N ⧸ Ideal.span {SymmetricAlgebra.ι R N s - 1}`.
- The morphism induced by the canonical R-algebra structure: `Spec.map` of
  `CommRingCat.ofHom` applied to `algebraMap R B`, precomposed with
  `ULift.ringEquiv.toRingHom`.
- Identification as an open subscheme: `IsOpenImmersion (Spec.map ...)`.
- Exactly the open subset V: the second conjunct is `Set.range (Spec.map ...) = ...`, with
  membership `s ∉ (p.asIdeal.comap ULift.ringEquiv.symm.toRingHom) • (⊤ : Submodule R N)`.
  Ideal action on the full submodule is precisely pN, consisting of finite sums of
  scalar multiples by elements of p. This is scheme identification, including the
  structure sheaf, because the map is an open immersion, rather than just a bijection.
  Affineness follows from the source being Spec(B); the node's “equivalently” clause
  describes this same consequence and is not an additional independent assertion.

Universe detail: R and N have independent universes u and v. Since B lives in max(u,v),
Mathlib's spectrum map requires lifting R to `ULift.{v} R`. The ring equivalence
`ULift.ringEquiv : ULift.{v} R ≃+* R` canonically identifies its spectrum with Spec(R).
The inverse equivalence transports each prime ideal in the image condition back to R.
This changes no mathematical object or hypothesis and permits modules in every universe.

Dependency declarations read and used:

- `lem-weil-pbc-symmetric-algebra-universal-property` is a Mathlib leaf:
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`, `SymmetricAlgebra` (50),
  `SymmetricAlgebra.ι` (60), ring/algebra instances (76–94), `SymmetricAlgebra.lift`
  (99), `SymmetricAlgebra.lift_ι_apply` (113), `SymmetricAlgebra.algHom_ext` (120).
  Read their full signatures and docstrings. Its existing notion is used directly.
- `def-weil-affine-spectrum` is a Mathlib leaf: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` (470), `AlgebraicGeometry.Spec.map` (479).
  Read the definition and map signature/docstring; no replacement spectrum is defined.
- Additional existing Mathlib operations: `Module.rankAtStalk` in
  `Mathlib.RingTheory.Spectrum.Prime.FreeLocus` (183), `IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion` (38), and ideal/submodule action in
  `Mathlib.Algebra.Algebra.Operations` (107). These give the notions explicitly
  spelled out in the node, without introducing a separate private definition.

Edge cases checked mathematically: R the zero ring has empty spectrum, so the local-rank
condition is vacuous and both loci are empty. For N=R and s=a, B=R[t]/(at-1) is R_a and
the locus is D(a). At a=0 the quotient is the zero ring and the locus is empty; at a=1
it is R and the whole spectrum. Nontrivial invertible modules are included because no
basis or global freeness is assumed. No field, characteristic, nonzero-section, domain,
Noetherian, or nonempty-spectrum hypothesis is imposed.

Searches actually run using `/home/ubuntu/weil-launcher/msearch.py`:

- LeanSearch: “The spectrum of the symmetric algebra of an invertible module modulo s
  minus one is the open nonvanishing locus of s”: unavailable, Internal Server Error.
- LeanFinder: “affine scheme nonvanishing locus section invertible module symmetric
  algebra quotient”: eight results on basic opens, ideal sheaves and tilde sections;
  none state this theorem.
- Loogle: `SymmetricAlgebra.ι`: twelve results, giving the symmetric-algebra inclusion
  and universal property, not the quotient's spectrum identification.
- Mathlib grep: `nonvanishing|invertible.*module|SymmetricAlgebra.*quotient` in
  AlgebraicGeometry: zero hits.
- Direct rg searches of Mathlib for `Invertible|rankAtStalk|IsLocallyFree` found local
  rank in FreeLocus; source reading confirmed its meaning.
- Direct rg searches of `WeilConjectures` and `lean/Sheaf` for invertible modules,
  local rank one, and nonvanishing found unrelated coordinate-cover and sheaf results.
  None states this algebra theorem. Plain grep of `WeilConjectures` for the item id
  returned no hit. Search of `dag/lean_names_upstream.json` for the item id,
  `affine_cap_section`, and `nonvanishing` returned no exact declaration.
- The chosen full theorem name was searched in the project Lean and upstream name list;
  it is new.

Server single-file compile passed with no errors or warnings. No statement dispute or
node correction was found.

The initial dry run exposed a preflight parser limitation: it treated `:=` in statement-local
`let` bindings as the beginning of the proof. The final signature spells out the quotient
and spectrum map directly, with identical mathematical content.

## Second reading by K1

Independently read the item JSON and its complete Lean module, both statement dependency
nodes and their recorded Mathlib declarations. Read the actual Stacks TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex,
label `lemma-affine-cap-s-open`, including its lemma and complete algebra proof;
also checked https://stacks.math.columbia.edu/tag/01PV. The algebra problem is over an
arbitrary commutative ring and an invertible module, without any ambient Noetherian,
field, separatedness, characteristic or nonemptiness assumption. No correction record,
new node or dependency module occurs in this delivery.

Object/hypothesis/conclusion checklist, written independently from the node:

1. Arbitrary commutative ring R: `(R : Type u) [CommRing R]`. Exact; neither a field nor
   a nontrivial ring is required.
2. R-module N: `(N : Type v) [AddCommGroup N] [Module R N]`. Exact, with its universe
   independent of R's.
3. N finite projective of rank one: `[Module.Finite R N] [Module.Projective R N]` and
   `(_hN : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = 1)`. Exact. Opened
   `FreeLocus.lean`: rankAtStalk is the natural-valued finrank of N_p over R_p. Finite
   projectivity makes these localizations finite free, so finrank one here is precisely
   locally free rank one, including modules without a global basis. It is not an
   unsupported global-rank condition or a finite-free assumption.
4. Symmetric algebra A and canonical inclusion iota: `SymmetricAlgebra R N` and
   `SymmetricAlgebra.ι R N`. Exact. Read the recorded universal-property dependency:
   in `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`, the ring-congruence quotient of
   the tensor algebra, its inclusion, CommRing instance, lift equivalence, evaluation
   formula and extensionality have exactly the dependency's signatures and meaning.
5. Element s: `(s : N)` after the module assumptions. Exact, arbitrary, including zero.
6. B=A/(iota(s)-1)A: `SymmetricAlgebra R N ⧸ Ideal.span
   {SymmetricAlgebra.ι R N s - 1}`. Exact: singleton ideal span is the principal ideal,
   and the quotient uses its canonical R-algebra structure.
7. Canonical morphism Spec(B) -> Spec(R): `Spec.map (CommRingCat.ofHom
   ((algebraMap R B).comp ULift.ringEquiv.toRingHom))`, with B expanded in the file.
   Exact after canonical universe transport. Read the affine-spectrum dependency and
   `Scheme.lean`: Spec is the scheme of prime ideals with its structure sheaf, and
   Spec.map is contravariantly induced by the ring map. Its domain is Spec(B), and its
   codomain Spec(ULift R). Read `ULift.ringEquiv`: down with inverse up. It gives a
   canonical identification of this codomain with Spec(R); no base change of content.
8. Identification with an open subscheme: the first conjunct `IsOpenImmersion (...)`.
   Exact: opened `OpenImmersion.lean`, where this is the locally ringed space open
   immersion property. It includes the structure sheaf, not only the underlying space.
9. Image exactly V={p | s not in pN}: the second conjunct `Set.range (...) = {p |
   s ∉ (p.asIdeal.comap ULift.ringEquiv.symm.toRingHom) • (⊤ : Submodule R N)}`.
   Exact. Read Ideal.comap (preimage) and the submodule scalar action in
   `Algebra.Algebra.Operations`: this is the submodule of finite sums a*n with a in
   the transported prime. The inverse ring equivalence is in the correct direction
   R -> ULift R. This expresses pN, not just individual scalar multiples.
10. V affine: follows from clauses 7-9 identifying the scheme Spec(B) with V. The node
    calls this equivalent; no extra independent assertion is missing. All quantifiers
    are universal in the stated order and no conclusion is strengthened.

Edge cases: the zero ring has empty prime spectrum and gives empty source and image;
local rank one is then vacuous, appropriately. A zero module over a nonzero ring fails
rank one, as it should; over the zero ring it is covered. For N=R, s=a gives
R[t]/(at-1), the principal localization with image D(a). At s=0 the ideal is the unit
ideal, B is zero and V empty; at a=1 the map identifies the whole spectrum. No index
set or numerical parameter n occurs in this statement, so empty index and n=0 impose
no extra restriction. Every characteristic and independent universe u,v is admitted:
the ULift to max(u,v) lets Mathlib use a common scheme universe without restricting N.

Independent searches (different phrasing from the first reader): msearch LeanFinder
`symmetric algebra rank one module quotient section minus one spectrum open immersion`
returned eight basic-open, localization, formally-unramified and Proj open-immersion
results, no exact symmetric-algebra quotient theorem. msearch Loogle `SymmetricAlgebra`
returned twelve constructor/universal-property results, none with the required image.
Direct rg `SymmetricAlgebra` on Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf
returned no hits. The broader rg `rankAtStalk|nonvanish|invertible.module` found local-rank
and invertible-sheaf results, not this algebra statement. The chosen theorem name has
no occurrence in the source/project or upstream name list. These corroborate the
worker's recorded LeanSearch outage and searches; existing Mathlib notions are used
without private copies, and no missing definition node is needed.

No mismatch found, so no Lean or node change was made. All four node proof steps and
all their cited dependencies occur in the declaration docstring. Both docstrings give
the source and blueprint id; there is one theorem, proved only by sorry, no definition
with postponed data, and no unbound variable or universe. Server single-file compile
passed cleanly in 1.7 seconds (exit 0). The initial reviewer compile invocation used a
repository-relative path; rerunning with the absolute sandbox path succeeded.
Second reading changes only this independent review section of the report.
