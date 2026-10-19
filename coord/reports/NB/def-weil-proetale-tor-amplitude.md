## Worker report

Defines `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` and
`AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude` in
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`. Both are real Prop-valued definitions;
there are no theorems, proofs, axioms, or sorry terms in this delivery.
The node and its dependency list are unchanged except for the added `lean` record.

Source checked: Stacks Project, `sites-cohomology.tex`, Definition
`definition-tor-amplitude`, Tag 08FZ, clauses (1) and (2), lines 12376--12395.
The definition is for a general ringed site, specialized here to the stated constant
coefficient sheaf on the small pro-etale site. Clause (3), local finite Tor dimension,
is not part of this node and is not introduced.

Clause-by-clause correspondence:

- A scheme is `(Y : Scheme.{t})`; the commutative ring is `(A : Type t) [CommRing A]`.
  The universe follows the recorded pro-etale site dependency, preserving its object
  universe `t+1` and morphism universe `t`, with no equality imposed between them.
- The small site is `ProEt.topology Y`. The body names `R`, the image of
  `CommRingCat.of (ULift A)` under `constantSheaf`, and `S`, its image under
  `sheafCompose ... (forget₂ CommRingCat RingCat)`. This is exactly the coefficient
  sheaf used in the recorded `proEtaleDerivedCategory`; no separate ring sheaf is defined.
- The module category is `C := ringedSiteModules.{t+1} S`, the transparent recorded
  abbreviation for Mathlib's `SheafOfModules S`. Every test object `(M : C)` is an
  arbitrary module sheaf, without flatness, finiteness, or constructibility assumptions.
- `(K : proEtaleDerivedCategory Y A)` is the stated derived object.
  `HasDerivedCategory.standard C` is the same localization instance as in that abbrev.
- `(a b : ℤ)` and the conjunct `a ≤ b` give an ordered integer interval. Putting this
  order condition in the predicate makes invalid intervals false and includes every
  ordered interval in the node. In particular, the one-point case `a=b` is allowed.
- `((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)` places precisely
  the test module in degree zero.
- The recorded tensor dependency is representative-based, not a bifunctor on derived
  objects. The definition therefore universally quantifies over cochain complexes
  `L P`, an isomorphism class witness `Nonempty (DerivedCategory.Q.obj L ≅ K)`, a
  morphism `f : P ⟶ L`, its quasi-isomorphism proof `hf`, and the recorded K-flat
  predicate `hP`. It then uses exactly `derivedTensor Y A L (single ... M) P f hf hP`.
  This quantification does not supply or choose a tensor operation or an arbitrary map.
  Every derived object has a representing cochain complex and every such complex has
  a K-flat resolution. Any of these resolutions computes its derived tensor; hence
  requiring vanishing on all of them is precisely the invariant condition on `K` in
  the node, not an additional hypothesis or a restriction on its objects. An iso is
  used rather than equality of chosen representatives. The tensor dependency ignores
  the particular comparison map when forming the total tensor, as its source shows.
- `(DerivedCategory.homologyFunctor C i).obj ...` is exactly the recorded cohomology
  sheaf functor; `IsZero` expresses zero in the abelian module-sheaf category.
- `(i : ℤ)` with `(i < a ∨ b < i)` means every degree outside the closed interval.
- `∃ a b : ℤ, HasProEtaleTorAmplitude Y A K a b` is finite Tor amplitude. The bounds
  precede all test sheaves and all representatives, so they are uniform in `M`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` (from the tensor module).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor`; this dependency is a Mathlib leaf with a
  `mathlib_match`, not a missing Lean record. `homologyFunctorFactors` explains its
  identification with cohomology of a representing cochain complex.
- `Sheaf.Algebra.Homology.DerivedTensor`, `AlgebraicGeometry.Scheme.derivedTensor`.
  Read the current live source with `scompile.py --source` and its full signature.
  The transitive `CochainComplex.IsKFlat` is the tensor dependency's recorded predicate.

Edge cases checked mathematically: the zero derived object and zero coefficient ring
have zero tensor cohomology in every degree, hence satisfy every ordered interval;
the empty scheme gives the same zero test; `a=b` tests all degrees except that degree;
negative degrees are included because all degrees and bounds are integers; no
boundedness, nonemptiness, or nonzero-ring hypothesis is imposed. A non-flat test
module is still quantified, so the definition detects Tor rather than merely ordinary
cohomological support. Finite amplitude uses a global interval, not bounds depending
on the module. The representative quantification is nonvacuous by existence of
representatives and K-flat resolutions, including for the zero object.

Searches performed with `msearch.py NB def-weil-proetale-tor-amplitude`:

- `leanfinder`, query `Tor amplitude of a derived complex of sheaves of modules on a
  ringed site`: eight generic derived-category t-structure/support results, no match.
- `loogle`, query `HasTorAmplitude, torAmplitude`: no hits, unknown identifier
  `HasTorAmplitude`.
- `grep`, query `torAmplitude|HasTorAmplitude|FiniteTorAmplitude`: no Mathlib hits.
- `leansearch`, query `Tor amplitude derived tensor sheaves modules`: service
  unavailable, Internal Server Error. This is not treated as a negative result.
- `rg` over upstream `WeilConjectures`, the side framework, and `lean/Sheaf` for
  `torAmplitude|TorAmplitude|finiteTor|FiniteTor|tor.?[Aa]mplitude`: found upstream
  `DerivedCategory.torAmplitudeIn` and `finiteTorAmplitude`, and the pro-etale
  specialization on `DerivedCategory (Sheaf J A)`; read both defining modules.
  The generic definition requires a derived monoidal structure on its category;
  the pro-etale specialization takes sheaves valued in a monoidal coefficient
  category, not the recorded `SheafOfModules S` category and its representative
  tensor interface. Neither provides this statement on the recorded objects.
  The present predicates use that interface directly and introduce no second
  derived tensor, category, cohomology functor, or K-flat predicate.
- `rg` for the node id in upstream source: no hit. `rg` for both proposed declaration
  names in `dag/lean_names_upstream.json`, upstream source and `lean/Sheaf`: no hit.

Validation: `scompile.py NB def-weil-proetale-tor-amplitude` compiled the sandbox module
and its library-path version cleanly (2.6 s and 2.4 s respectively), with no warnings.
Delivery dry-run validation follows below when complete. No statement dispute or
missing prerequisite was found; no new nodes or dependency repairs were needed.

## Second reading by NB

Independently read the sandbox node and module against Stacks
`sites-cohomology.tex`, Definition `definition-tor-amplitude` (08FZ),
clauses (1) and (2), including the opening ringed-site assumptions. The
source requires only a ringed site, a derived object, and ordered integer
bounds; it imposes no Noetherian, nonempty, flatness, characteristic, or
finiteness hypothesis. This node specializes the site and ring sheaf.

Object/hypothesis/conclusion inventory and Lean correspondence:

1. An arbitrary scheme Y: `(Y : Scheme.{t})`. Pass: no extra scheme property.
2. An arbitrary commutative ring A: `(A : Type t) [CommRing A]`. Pass: no field,
   nontriviality, characteristic, or finiteness requirement. The common size
   parameter is the recorded site/derived-category convention; differently
   sized scheme and coefficient data can be placed in a common larger
   universe. Site object and morphism universes remain t+1 and t respectively.
3. Small pro-etale site and constant commutative ring sheaf A_Y:
   `ProEt.topology Y`, `R := (constantSheaf ... CommRingCat).obj
   (CommRingCat.of (ULift A))`, and its forgotten ring sheaf S. Pass: these
   are the exact expressions in `proEtaleDerivedCategory`, not private copies.
4. The abelian category Mod(A_Y): `C := ringedSiteModules.{t+1} S`. Pass:
   read the dependency abbreviation; it is exactly `SheafOfModules S`.
5. Derived object K: `(K : proEtaleDerivedCategory Y A)` and
   `HasDerivedCategory.standard C`. Pass: the same localization instance
   appears in the recorded abbreviation; neither boundedness nor a chosen
   resolution is assumed of K.
6. Integers a <= b: `(a b : ℤ)` and the conjunct `a ≤ b`. Pass: agrees on
   every ordered interval. The additional extension of the predicate to
   unordered pairs is false and makes no assertion beyond the node's domain.
7. Every module sheaf M, in degree zero: `(M : C)` and
   `(HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M`. Pass: all
   module sheaves are tested, including nonflat and nonconstructible ones.
8. Derived tensor K tensor^L M: quantify over `(L P : CochainComplex C ℤ)`,
   `Nonempty (DerivedCategory.Q.obj L ≅ K)`, `f : P ⟶ L`, `hf : QuasiIso f`,
   and `hP : CochainComplex.IsKFlat ... P`; apply the recorded
   `derivedTensor Y A L (single ... M) P f hf hP`. Pass: read the full live
   tensor source with `scompile.py --source`, and the K-flat definition.
   Its body is Q of the total tensor P tensor M; it does not choose arbitrary
   data. Stacks 06YS (`lemma-K-flat-resolution`) provides resolutions of
   every complex, and the construction preceding `definition-derived-tor`
   shows independence of resolutions. Localization has representatives up
   to isomorphism. Thus the universal formulation is nonvacuous and tests
   precisely the derived tensor on K, with no additional mathematical
   hypothesis. K-flatness is defined with tensor on the other side; symmetry
   over the commutative ring sheaf identifies these conditions.
9. Cohomology sheaves vanish in every degree outside [a,b]: `(i : ℤ)`,
   `i < a ∨ b < i`, and `IsZero ((DerivedCategory.homologyFunctor C i).obj
   ...)`. Pass: read `homologyFunctor` and `homologyFunctorFactors` in
   Mathlib; these are the localization-induced cohomology functors, and
   categorical IsZero is the correct zero-sheaf condition.
10. Finite amplitude: `∃ a b : ℤ, HasProEtaleTorAmplitude Y A K a b`.
    Pass: a single ordered interval precedes every test module and degree;
    bounds cannot depend on M. No local finite dimension clause is added.

All six dependency nodes were opened, including their complete statements
and Lean/mathlib records. Read the recorded project modules
`ProEtaleDerivedCategory`, `RingedSiteModules`, `DerivedTensor`, and the
transitive `KFlat`, as well as Mathlib's site, constant-sheaf, derived-category,
and homology signatures. No new nodes or dependency modules are delivered;
there is no statement_change requiring a citer audit.

Edge cases: the zero complex and zero ring give zero tensor cohomology in
all degrees; the empty scheme likewise yields the zero-sheaf case. These
are included without nonzero/nonempty assumptions. The singleton interval
`a=b`, particularly `[0,0]`, excludes exactly all other degrees. Negative
bounds and negative cohomology are included by integer indexing. There is
no index family whose emptiness could impose a hidden restriction. Every
characteristic is allowed. The explicit universe t and all object binders
are bound; no site-universe equality was introduced.

Independent H4 searches: ran msearch LeanFinder with `uniform boundedness
of cohomology after derived tensor with all module sheaves` (eight unrelated
sheaf-cohomology/category hits), Loogle with `"tor", "amplitude"` (no hits),
and grep with `tor.?dimension|[Tt]or[Aa]mplitude|[Tt]or[Bb]ound` (two unrelated
commutator-bound hits). Direct rg using Tor dimension/amplitude/bound and
finite-Tor variants inspected Mathlib's homology and module-sheaf trees,
upstream WeilConjectures, the side framework, and lean/Sheaf. Opened both
upstream `CategoryTheory/DerivedCategory/TorAmplitude.lean` and
`SixFunctors/ProEtale/Derived/TorAmplitude.lean`. The former needs a monoidal
closed braided Grothendieck category and a derived monoidal localization
instance; the latter is on `DerivedCategory (Sheaf J A)` for a coefficient
category A. Neither is the recorded SheafOfModules-category predicate with
the recorded representative tensor. They supply no directly usable exact
attachment here. The side framework's module-object realization is also a
different ambient category, as documented in coord/pefw-upstream-framework.md.
An rg search for the two delivered names in the project, upstream, side
framework and upstream-name registry found no collisions.

No mismatch found; the Lean and node record are unchanged. The module has
real Prop-valued bodies, no sorry data, no theorem proofs, no file-local
notation/instances, and source/blueprint docstrings for both definitions.
The node proof list is empty, so no proof narrative is omitted. The recorded
lean.statement is verbatim the main definition signature from `def` to `:=`.
Only this independent review section was added.
