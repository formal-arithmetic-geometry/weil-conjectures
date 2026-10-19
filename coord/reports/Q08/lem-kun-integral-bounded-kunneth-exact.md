## Worker report

The module `Sheaf.Algebra.Homology.IntegralBoundedKunnethExact` states
`DerivedCategory.integral_bounded_kunneth_exact`. Its only postponed proof is the
whole proof of this theorem, `sorry`. All five auxiliary definitions have real data:
the module-category specialization, the two direct sums, and the canonical maps on
these sums. They belong to the sequence specified by this node and are listed in
`lean.declarations`. No dependency node or additional definition node was needed.
The item's natural statement, proof, and dependencies are unchanged.

The source was read at Stacks More on Algebra, Tag 0H7Z,
`lemma-kunneth-spectral-sequence`, and Tag 0H80, `example-kunneth-dedekind`, in the
local cache, lines 15800–15850. The example states the displayed short exact
sequence for every integer degree, with bounded derived arguments supplied by
0H7Z and no finite-generation condition. Naturality follows from the canonical
filtered construction, as detailed in the node's fifth proof step. The theorem's
docstring carries all five node proof steps and their dependencies, including
higher integral Tor vanishing via a two-term flat resolution and extraction of
the two-piece finite filtration.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Abelian groups and integral coefficients: `IntegralModuleCat.{u}` is exactly
  `ModuleCat.{u} (ULift.{u} ℤ)`. An abelian group has a unique action of the integers;
  an action of their canonical ring lift is the same action with lifted scalars.
  Thus this encodes all abelian groups in universe `u`, with no added mathematical
  structure or restriction. Lifting the ring, rather than restricting the carrier
  universe, is necessary because Mathlib's module monoidal structure requires
  coefficients and carriers in the same universe. The category equivalence is
  the usual integral-module/abelian-group equivalence composed with restriction
  along `ULift ℤ ≃+* ℤ`; the statement needs no arbitrary comparison map.
- `D(ℤ)` and cochain cohomology: `DerivedCategory IntegralModuleCat.{u}` under
  `[HasDerivedCategory.{w} IntegralModuleCat.{u}]` and
  `homologyFunctor IntegralModuleCat.{u} i`. This is the recorded localization of
  integer-indexed cochain complexes, not homological indexing. The chosen
  localization universe `w` and carrier universe `u` are explicitly bound and
  independent, in accordance with the size convention.
- The hypothesis `C,D ∈ D^b(ℤ)`: both family arguments have type
  `Bounded IntegralModuleCat.{u}`, Mathlib's full subcategory for the bounded part
  of the standard t-structure. Its objects have finitely supported cohomology.
  It imposes no chain-level boundedness, projectivity, flatness, or finite generation.
- The ordinary K-flat derived tensor: `C.obj ⊗ D.obj` uses the existing upstream
  `DerivedCategory` monoidal instance, obtained from the K-flat left derivability
  structure. `DerivedCategory.hasDerivedMonoidalCategory` provides its interface.
  The construction derives the ordinary total tensor in both variables. Fixing
  the second complex computes the same left-derived tensor as the recorded
  `exists_derivedTensor_second_factor_functor` with the identity coefficient map;
  universal uniqueness identifies these constructions. No new derived tensor
  or arbitrary monoidal structure is introduced.
- Every integer `r`: the theorem binds `(r : ℤ)` without a positivity restriction.
- The left group: `integralKunnethTensorTerm r C D` is the categorical coproduct
  indexed by `{p : ℤ × ℤ // p.1 + p.2 = r}` of the tensor of `H^(p.1)(C)` and
  `H^(p.2)(D)`. In modules, this categorical coproduct is the direct sum, not a
  product. Each ordered pair occurs once.
- The middle group: `(homologyFunctor IntegralModuleCat.{u} r).obj
  (C.obj ⊗ D.obj)` is precisely `H^r(C ⊗ᴸ_ℤ D)`.
- The right group: `integralKunnethTorTerm r C D` uses the coproduct over
  `{p : ℤ × ℤ // p.1 + p.2 = r + 1}` of
  `((Tor' IntegralModuleCat.{u} 1).obj H^i(C)).obj H^j(D)`. This is the dependency's
  first-variable projective-resolution Tor, with Tor degree exactly one.
- Short exactness, including both terminal zeroes: the existential families `ι`
  and `π` are linear morphisms between exactly those three objects. For each pair,
  `Function.Injective (ι C D)` renders exactness at the left, `Function.Exact
  (ι C D) (π C D)` says image equals kernel in the middle, and
  `Function.Surjective (π C D)` renders exactness at the right. Over the lifted
  integers these are equally the conditions on abelian-group homomorphisms.
- Naturality in both arguments: the existential maps are chosen as whole families,
  before universal quantification over objects and derived morphisms. For every
  `f : C ⟶ C'` and `g : D ⟶ D'` the last two conjuncts are the inclusion and
  quotient commuting squares, with middle map `H^r(f.hom ⊗ₘ g.hom)`.
  `integralKunnethTensorMap` is `Limits.Sigma.map` of `H^i(f) ⊗ₘ H^j(g)`.
  `integralKunnethTorMap` is `Limits.Sigma.map` of the canonical composite of
  `Tor'.map` in the first argument and `.obj.map` in the second. Hence the
  exterior maps are prescribed tensor/Tor maps, not freely chosen witnesses.
  Taking either morphism to be an identity includes separate naturality.
- No finite-generation hypothesis: none is present. There is also no exponent,
  splitting, torsion, freeness, or finite-type hypothesis or conclusion.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`; cohomology is
  `DerivedCategory.homologyFunctor` from `...DerivedCategory.HomologySequence`.
  The full signatures and docstrings of the localization and cohomology functor
  were read, including `homologyFunctorFactors`.
- `def-weil-pbc-bounded-derived-subcategories` has a `mathlib_match` rather than a
  usable `lean` record: `Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
  `DerivedCategory.Bounded` and `.Bounded.ι`. Read `TStructure.bounded = plus ⊓ minus`
  and `DerivedCategory.isGE_iff` / `isLE_iff` to check the finite-cohomology meaning.
- `lem-pc-derived-tensor-second-factor-functor`:
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`,
  `DerivedCategory.exists_derivedTensor_second_factor_functor`; read its entire
  signature and proof docstring, including computation on K-flat models,
  comparison uniqueness, and functoriality in the second complex. Its existing
  module is publicly imported. The actual bifunctor is the existing upstream
  derived monoidal construction, not a copy of this dependency.
- `def-weil-pbc-tor-modules`: `Mathlib.CategoryTheory.Monoidal.Tor`,
  `CategoryTheory.Tor'`. Read the full definition and its docstring to check
  derivation in the first, rather than the second, factor.
- The stated proof dependencies are imported without `public`:
  `Sheaf.Algebra.Homology.FlatResolutionTorComparison` (`ModuleCat.flatResolution_torComparison`),
  `Mathlib.RingTheory.Flat.TorsionFree`
  (`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`),
  `Mathlib.Algebra.Homology.SpectralSequence.Basic` (`CategoryTheory.SpectralSequence`),
  and `WeilConjectures.CategoryTheory.Abelian.Filtration`
  (`CategoryTheory.DecreasingFiltration`). Their signatures/docstrings were read.
  `lem-kun-bounded-tensor-tor-spectral-sequence` has no recorded declaration; it is
  a proof prerequisite only, so there is no module to import and it is not needed
  to type the present statement.

Edge cases checked before writing: the zero derived object in either argument
makes every term zero; an acyclic representative has the same effect. For two
modules in degree zero, the sequence in degree zero gives the ordinary tensor,
while degree minus one gives Tor-one; this checks the crucial `r + 1` sign. Shifts
of either input shift the pair indices and the middle cohomology equally. Degrees
outside the finite cohomological supports contribute zero summands. The sums are
indexed over all integer pairs, including infinitely many zero summands, so no
choice of bounds or finite index set is needed. Infinite-rank free groups and
non-finitely-generated torsion groups are covered; no torsion exponent is fixed.
The universe lift includes the smallest universe and arbitrary larger universes.

Searches for existing statements and names (2026-10-16):

- `msearch.py ... leanfinder "Integral Kunneth short exact sequence for bounded derived
  complexes of abelian groups, natural in both arguments"`: eight hits, on
  `ShortExact.singleδ`, Ext sequences, and `DerivedCategory.HomologySequence.exact₁/₂/₃`.
  Their returned signatures concern a triangle or a single short exact sequence,
  not the tensor/Tor sequence of two derived objects. No exact match.
- `msearch.py ... loogle '"Tor", "ShortExact"'`: nine hits, on preservation of
  exactness, group (co)homology, a localization-size instance, and Mayer–Vietoris.
  None has this integral derived Kunneth statement.
- `msearch.py ... grep 'kunneth|Künneth|derivedTensor' Algebra/Homology`: no Mathlib hits.
- `msearch.py ... leansearch "Kunneth short exact sequence for bounded derived abelian
  groups over the integers"`: unavailable, Internal Server Error. This is recorded
  as an unavailable service, not a negative search result.
- `rg -n 'kunneth|Künneth|lem-kun-integral-bounded-kunneth-exact'` in upstream
  `WeilConjectures` and project `lean/Sheaf`: the existing Kunneth statements are
  field-linear Cech tensor statements and geometric Kunneth-Verdier comparisons;
  none is the integral bounded tensor/Tor exact sequence. Searching the item ID
  in upstream gave no matches. The field-linear `TensorKunneth` module cannot
  supply integral Tor-one terms.
- `rg -n 'IntegralModuleCat|integralKunneth|integral_bounded_kunneth_exact'` in
  Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream
  declaration-name inventory: no collisions with the delivered names.
- Direct searches for derived tensor and monoidal instances found
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal` and
  `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
  Read their definitions: these provide exactly the needed K-flat construction,
  so no new tensor definition or dependency repair was written.

No STATEMENT-DISPUTED flag or mathematical node fault was found. Compilation uses
only the prescribed `scompile.py` wrapper, with every variable and universe bound.
No global build or direct modification of a read-only checkout was performed.

## Second reading by Q08

I independently opened the item JSON, the delivered 133-line Lean module, all four
statement-dependency records, and their declaration sources. I read the Stacks
cache at `more-algebra.tex`, `lemma-kunneth-spectral-sequence` (0H7Z) and
`example-kunneth-dedekind` (0H80), including the preceding filtered tensor
construction in `section-kunneth-spectral-sequence`. The section starts with an
arbitrary ring and filtered complexes; the flat and K-flat representative
assumptions belong to the construction, not to the final derived objects. The
lemma assumes exactly bounded derived inputs, and the example specializes to
integers or a Dedekind domain. It prints the tensor sum in degree n and Tor sum
in degree n+1, with no finite-generation assumption. Naturality comes from the
filtered construction, as the node's proof explicitly records.

My checklist of objects, hypotheses, and conclusions, with the Lean rendering:

1. **All abelian groups and integer coefficients — PASS.**
   `IntegralModuleCat.{u} := ModuleCat.{u} (ULift.{u} ℤ)` is a reducible
   specialization of the existing module category. Every abelian group has its
   unique integer action; restriction along the canonical lifted-integer ring
   isomorphism changes no group or homomorphism. The lift permits arbitrary
   carrier universe u with Mathlib's same-universe monoidal module interface.
   This is an encoding of Ab, with no freeness, torsion, or cardinality condition.
2. **The cochain derived category D(Z) — PASS.**
   `[HasDerivedCategory.{w} IntegralModuleCat.{u}]` supplies the chosen localization
   of integer-indexed cochain complexes, and `DerivedCategory.homologyFunctor`
   factors their cohomology. I read `DerivedCategory`, `Q`, `homologyFunctor`, and
   `homologyFunctorFactors` in their Mathlib sources. The coefficient/carrier
   universe u and localization morphism universe w are independently bound.
3. **C and D have finitely supported cohomology — PASS.**
   Each argument is `Bounded IntegralModuleCat.{u}`. I checked
   `DerivedCategory.Bounded` in TStructure.lean, the underlying
   `t.bounded = t.plus ⊓ t.minus`, and `isGE_iff`/`isLE_iff`. These bound
   cohomology, without requiring any chosen representative to be bounded or flat.
   The subcategory is full, so its arrows include all derived morphisms.
4. **The ordinary K-flat derived tensor — PASS.**
   The middle object uses `C.obj ⊗ D.obj`. I read the imported
   `exists_derivedTensor_second_factor_functor` signature with its K-flat
   computation and naturality, and the upstream derived monoidal construction.
   `DerivedCategory.hasDerivedMonoidalCategory` uses K-flat left derivability;
   the monoidal instance derives the total tensor bifunctor on the homotopy
   category. Its fixed-second-factor restriction computes the same ordinary
   derived tensor as the recorded dependency, up to its canonical derived-functor
   comparison. `ModuleCat.hasFunctorialFlatResolution` provides the needed
   instance for every commutative ring in the carrier universe, so no extra
   hypothesis is silently required of C or D.
5. **Every integer r — PASS.** The explicit binder is `(r : ℤ)`.
   There is no lower bound or nonnegativity condition.
6. **Left direct sum — PASS.** `integralKunnethTensorTerm r C D` is the
   categorical coproduct over `{p : ℤ × ℤ // p.1 + p.2 = r}` of
   `H^(p.1)(C) ⊗ H^(p.2)(D)`. In modules the coproduct is the direct sum.
   Ordered pairs occur exactly once; no finite subset or product replaces it.
7. **Middle group — PASS.**
   `(homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj)`
   is H^r of precisely the preceding derived tensor, with cohomological indexing.
8. **Right direct sum — PASS.** `integralKunnethTorTerm r C D` uses the
   pair condition `p.1 + p.2 = r + 1` and
   `((Tor' IntegralModuleCat.{u} 1).obj H^(p.1)(C)).obj H^(p.2)(D)`.
   I opened `CategoryTheory.Tor'`: it left-derives tensoring on the right,
   hence resolves its first module argument, exactly the dependency node's Tor.
   The Tor degree is one, not r or an absolute value of an index.
9. **There is a short exact sequence, including both zero ends — PASS.**
   The witnesses `ι` and `π` are module morphisms between these exact three
   objects. `Function.Injective`, `Function.Exact`, and `Function.Surjective`
   express respectively exactness at the left, middle, and right groups.
   All additive homomorphisms are integral-linear, so module morphisms add no
   restriction here. No splitting or canonical splitting is asserted.
10. **Naturality in both derived arguments — PASS.**
    For fixed r, the existential witnesses are families over all C,D before
    the exactness and naturality quantifiers. The last two conjuncts quantify
    over every `f : C ⟶ C'`, `g : D ⟶ D'` and state both commuting squares.
    The middle arrow is `H^r(f.hom ⊗ₘ g.hom)`. The exterior arrows are prescribed:
    `integralKunnethTensorMap` is the coproduct of cohomological tensor maps;
    `integralKunnethTorMap` is the coproduct of the first-variable Tor map at
    H^j(D), followed by the second-variable map at H^i(C'). I checked the
    definition of `Limits.Sigma.map`, so these maps have the required summand
    action. Identities in either variable give separate naturality as well.
11. **No finite generation — PASS.** No binder imposes finite generation,
    finite presentation, a common exponent, flat cohomology, or projectivity.

Edge cases: the actual index subtype is nonempty for every r (for example
(r,0)), and using an unrestricted coproduct also handles degrees in which every
summand vanishes. The zero derived input is allowed, as are acyclic
representatives. For C=M[0], D=N[0], degree zero yields ordinary tensor and
degree minus one yields Tor-one; M=N=Z/2 confirms the r+1 sign. Shifts to
cohomological degrees a,b put tensor in a+b and Tor-one in a+b-1. Free input
kills the latter. Arbitrary infinite direct sums of torsion groups and
infinite-rank free groups remain covered. u=0 and arbitrary larger u are
allowed; w has no imposed equality with u. There is no scheme, empty-scheme,
or variable-characteristic hypothesis in this integral algebraic statement.

Independent duplicate searches, using different vocabulary from the worker:

- `msearch.py Q08 lem-kun-integral-bounded-kunneth-exact leanfinder` with
  "Universal coefficient sequence for hyperhomology of the tensor of two bounded
  complexes over the integers, with homology tensor and first Tor terms natural
  in both variables": eight hits, all ordinary tensor-complex existence,
  associativity, summand inclusion, and tensor-object infrastructure. The
  returned signatures do not state a cohomological tensor/Tor exact sequence.
- `msearch.py ... loogle '"Tor", "Exact"'`: twelve hits, including
  `Function.Exact.rangeFactorization`, its equivalence, and bundled exact
  functors. Read the signatures: these provide exactness infrastructure rather
  than the integral derived statement. No exact match.
- `msearch.py ... grep` for hyper-Tor, Kunneth, universal coefficient, and
  Tor/bounded combinations in `Algebra/Homology`: four substring hits in
  bounded homotopy/derived-functor infrastructure; none states this result.
- Independent `rg` searches of upstream `WeilConjectures`, project `lean/Sheaf`,
  Mathlib's monoidal folder, and the upstream declaration inventory found no
  collision with `IntegralModuleCat`, `integralKunneth*`, or the theorem name.
  I opened the field-linear `HomologicalComplex.tensor_kunneth` signature and
  upstream `Etale.nonempty_iso_kunneth`: the former assumes a field and has no
  Tor term; the latter compares geometric global sections. Neither is the
  present integral sequence. The general Tor and derived-tensor definitions
  already exist and are used, rather than reconstructed.

H4/H5/H6/H8/H9 audit: the five helpers are just the category abbreviation, the
two specified sequence terms, and their prescribed morphisms. They use real
Mathlib/upstream constructions and belong to this sequence, so no independent
missing notion, new definition node, or dependency repair is needed. The only
postponed theorem is `integral_bounded_kunneth_exact`, whose whole proof is
`sorry`; its docstring reproduces all five node proof steps and dependency IDs.
All six declarations and the module have source/blueprint docstrings. The
imports include all currently recorded proof-dependency modules; the bounded
Tor spectral-sequence prerequisite has no declaration to import. I also read
the flat-resolution comparison signature, spectral-sequence page rule,
PID-flatness lemma, and the current filtration source (via `scompile.py --source`
because that source file is absent from the older upstream checkout).

No mathematical mismatch or invalid node statement was found. I retained the
Lean module, node statement, proof, and dependency list unchanged. The
`lean.statement` is verbatim equal to the source signature, all variables and
universes are explicitly bound, every source line is at most 100 characters,
and only the theorem proof contains `sorry`. This second reading adds this
independent audit and its actual search log. `scompile.py Q08
lem-kun-integral-bounded-kunneth-exact
lean/Sheaf/Algebra/Homology/IntegralBoundedKunnethExact.lean` completed cleanly:
the wrapper's sandbox and module checks both exited zero, with no warnings.
