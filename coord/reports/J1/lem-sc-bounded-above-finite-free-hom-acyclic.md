## Worker report

The module `Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic` states
`CochainComplex.acyclic_homComplex_of_boundedAbove_finiteFree`; its only proof is `sorry`.
No definition, new node, dependency replacement, or statement correction is introduced.
The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- The ringed site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`
  with `{R : Sheaf J CommRingCat.{w}}`. Forgetting commutativity through
  `(sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R` supplies exactly
  the coefficient sheaf expected by Mathlib's `SheafOfModules`.
- Both complexes are `CochainComplex (SheafOfModules.{w} ...) ℤ` in the binder `(E A : ...)`.
  They therefore have the same ring, site, and integer cochain grading as the node.
- Bounded above for E is `hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p)`.
  This concerns the terms themselves, not just cohomology.
- Finite-rank free in every degree is `hEfree : ∀ p : ℤ, ∃ r : ℕ,
  Nonempty (E.X p ≅ SheafOfModules.free (R := ...) (ULift.{w} (Fin r)))`.
  Mathlib's `free` is the coproduct of copies of its rank-one `unit`, so this is exactly
  isomorphism to a finite direct sum of the coefficient sheaf. The rank is allowed to
  vary with p, and `Nonempty` asks only for existence of the isomorphism.
- Bounded below for A is `hAbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (A.X q)`.
- Acyclicity of A is `hAacyclic : A.Acyclic`, using the recorded Mathlib predicate.
- The entire conclusion is `(CategoryTheory.homComplex E A).Acyclic`, using the
  dependency's sheaf-valued total Hom, rather than the complex of global morphism groups.

The infrastructure instances are those needed for the dependency constructions:
`J.HasSheafCompose` forgets commutativity; `HasWeakSheafify` and
`J.WEqualsLocallyBijective` at w construct the free sheaves and abelian category,
and at `max u v w` give the abelian category containing the Hom output. They express
sheafification/local exactness infrastructure for the abelian sheaf-module categories
already specified in def-weil-sheaf-of-modules-category, not a finiteness, freeness,
projectivity, or geometric assumption on the complexes or site. All three universe
variables are explicit and unrestricted. The Hom dependency raises its output module
universe to `max u v w`; this is preserved. No assumption that the site is topological
or that stalk rings are local is imposed.

Dependencies inspected and used:

- def-weil-sheaf-of-modules-category: `SheafOfModules` in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`, with the abelian instance from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- def-pc-cochain-complex-modules: `CochainComplex` in
  `Mathlib.Algebra.Homology.HomologicalComplex` (imported via the Hom dependency).
- def-pc-acyclic-complex-modules: `HomologicalComplex.Acyclic` in
  `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`; this means exact at every
  degree and is equivalent to vanishing homology in the abelian category.
- def-pur-hom-complex: `CategoryTheory.homComplex` in
  `Sheaf.Algebra.Homology.HomComplex`. Read its full module, including
  `homComplex_exists` and its product projection and signed differential specification.
- def-weil-locally-ringed-space-morphism: read the recorded
  `AlgebraicGeometry.LocallyRingedSpace.Hom` in
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`. This dependency describes ringed
  spaces and their morphisms; the present node merely uses a ringed site, which is
  already supplied by the site and coefficient sheaf above. Its morphism declaration
  is not needed, and importing it or binding a locally ringed space would incorrectly
  restrict the node to topological sites with local stalks. No dependency module is
  needed to state the site, since the sheaf-module-category dependency supplies it.

Also read the free sheaf signature and docstring in
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`, and the already landed
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`, whose finite-free
hypothesis uses the same `free`/`ULift (Fin r)` representation. That theorem is a proof
dependency, so it is cited in the natural-language proof but not imported by the statement.

Edge cases: rank zero is included by r = 0; zero E and zero A are allowed; bounds may be
any integers, including negative ones; E need not be bounded below and A need not be
bounded above; no uniform finite rank is required. An empty site and zero coefficient
ring are not excluded. The proof docstring records the finite interval of lifting degrees,
local rather than global lifts, and the last degree M where cycles vanish because A has
no preceding term. There is no assumption of global splitting or global projectivity.

Searches (2026-10-11):

- msearch.py leanfinder, query `bounded above finite free sheaf complex internal Hom
  bounded below acyclic`: eight hits about derived single-object maps and T-structure
  bounds, no sheaf-valued Hom acyclicity theorem.
- msearch.py loogle, query `SheafOfModules, free, homComplex`: zero hits, unknown
  identifier `free` in the remote index.
- msearch.py leansearch, query `bounded above finite free sheaf Hom complex bounded
  below acyclic`: service unavailable (Internal Server Error); no verdict from this tool.
- msearch.py grep, query `acyclic.*homComplex|homComplex.*acyclic|finiteFree.*Hom|free.*hom.*acyclic`:
  four hits, all KInjective/KProjective comments about morphism-group Hom complexes.
- rg of Mathlib's ModuleCat/Sheaf sources for free/finiteFree/IsFree found `unit` and
  `SheafOfModules.free`; their definitions were read and reused.
- rg of WeilConjectures and lean/Sheaf for `acyclic.*homComplex|homComplex.*acyclic|
  acyclic.*finiteFree`: no exact theorem. The upstream item-id search also had no hit.
- rg of `dag/lean_names_upstream.json`, Mathlib, WeilConjectures, and lean/Sheaf for
  the proposed full declaration name: no collision. Project finite-free searches found
  the existing finite-free internal-Hom exactness theorem, which has a different conclusion.

Source checked online because this machine does not have literature/stacks-project/cohomology.tex:
[Stacks Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8), case (2).
The full source proves a stalk comparison; this node isolates the auxiliary Hom-acyclicity
calculation in its proof route. The site's formulation is justified by the node's explicit
local lifting proof, which uses finite free terms and local exactness only.
No mathematical statement dispute was found.

Validation: scompile.py compiled the module on the server with exit code 0, in 1.5 seconds,
with no errors or warnings. The second reading is intentionally left for the independent reader.

## Second reading by J1

Independent second reading, 2026-10-11. Opened the sandbox node and Lean module,
all five statement dependency nodes and their recorded declarations, the Hom-complex
module (including its existence specification), and the upstream internal sheaf Hom.
No mathematical or Lean-signature mismatch was found. The module and node are unchanged;
this section adds the independent reading and more precise source/search evidence.

The node's complete object, hypothesis, and conclusion list, with its Lean rendering:

1. A ringed site `(U, O_U)`: `{C : Type u} [Category.{v} C]`,
   `{J : GrothendieckTopology C}`, and `{R : Sheaf J CommRingCat.{w}}`.
   Verdict: same general site and commutative coefficient sheaf. The forgetful
   `sheafCompose` supplies the ring sheaf for `SheafOfModules`; it does not change
   coefficients. The ringed-space dependency's `LocallyRingedSpace.Hom` was read
   (base morphism and local stalk-map property): neither a morphism nor local stalks
   is an object of this statement, so importing or binding it would add hypotheses.
   The existing sheaf-module dependency already supplies the general site formulation.
2. Two cochain complexes of sheaves of these modules: `(E A : CochainComplex
   (SheafOfModules.{w} ...) ℤ)`. Verdict: same coefficient sheaf and all integer
   degrees for both complexes. `SheafOfModules` has an underlying presheaf of modules
   with the sheaf condition; its morphisms are module-presheaf morphisms.
   `CochainComplex` specializes `HomologicalComplex` to shape `up ℤ`, with square-zero
   differentials and commuting complex morphisms. No private definitions are used.
3. E bounded above: `hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p)`.
   Verdict: vanishing terms, exactly as required, rather than merely vanishing cohomology.
4. Every term of E finite-rank free: `hEfree : ∀ p : ℤ, ∃ r : ℕ,
   Nonempty (E.X p ≅ SheafOfModules.free (R := ...) (ULift.{w} (Fin r)))`.
   Verdict: globally free sheaves of finite rank, not just locally free sheaves or
   projective objects. Read `SheafOfModules.unit`, `free`, and `freeHomEquiv`:
   `unit` is the coefficient sheaf as a module and `free` is its coproduct indexed by
   the specified type. For `Fin r` this is precisely the finite direct sum.
   The existential rank follows the universal degree, allowing varying ranks;
   `Nonempty` asks only for existence of an isomorphism.
5. A bounded below: `hAbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (A.X q)`.
   Verdict: termwise vanishing below an arbitrary integer, with no upper bound on A.
6. A acyclic: `hAacyclic : A.Acyclic`. Verdict: the recorded predicate
   `HomologicalComplex.Acyclic = ∀ i, K.ExactAt i`; read
   `exactAt_iff_isZero_homology`, which identifies this with zero cohomology sheaves.
7. The entire conclusion, the total sheaf Hom complex is acyclic:
   `(CategoryTheory.homComplex E A).Acyclic`. Verdict: exactly the conclusion.
   `homComplex_exists` specifies product terms over p, internal sheaf Homs to
   `A.X (p+n)`, and differential `d_A f - (-1)^n f d_E`.
   Its chosen data supply `homComplexFunctor` and `homComplex`, so this is not an
   unspecified complex, nor the complex of global morphism groups.

Infrastructure and universes: the five class binders provide forgetting commutativity,
sheafification, and the identification of local bijectivity with sheafification equivalence.
At w these provide the free construction and the abelian category used for A; at
`max u v w` they provide the abelian category of internal Homs. This agrees with the
small-relative-to-module-universe qualification in the sheaf-module dependency.
The parameters u, v, w are explicit and have no imposed equality or inequality;
taking a universe containing the site gives the usual arbitrary small-site case.
The raised Hom universe is forced by the existing `homObj` dependency, not a geometric
restriction. There is no Noetherian, field, characteristic, point, local-ring,
projectivity, or nonemptiness assumption. All variables and universes are bound.

Edge cases: `r = 0` gives the empty coproduct; zero E and zero A are allowed. Empty
sites and the empty ringed space have no excluded nonempty binder. Arbitrary zero
rings and all characteristics (including two, where signs coincide) are included.
Degree zero and negative degrees use the same ℤ grading. The bounds can cross, leaving
an empty finite interval of components. No uniform rank bound, lower bound on E,
or upper bound on A is imposed. ULift preserves the finite index set and its empty case.

Source reading: fetched the Stacks cohomology.tex source into the sandbox and read
`lemma-stalk-internal-hom` (Tag 0GM8), case (2), together with its cited
`lemma-pullback-internal-hom`, case (2), and `lemma-local-lift-map` /
`lemma-local-homotopy`. See [Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8).
The literal tagged theorem is a derived stalk comparison, not this auxiliary acyclicity
lemma; its proof invokes the pullback lemma. This node isolates the finite-free Hom
calculation in that route and explicitly states it for sites. The source assumes a
ringed space, not a locally ringed space, and adds no Noetherian or characteristic
hypothesis. The extension of the auxiliary calculation to the node's sites uses only
finite local lifts and finite covering refinements. The Lean exactly retains the
node's global term bounds and free terms. No statement correction is needed.

Checked the proof docstring against both node proof steps and the dependency's signs.
For h of degree m-1 the sign is `+ (-1)^m`, and the cocycle equation gives
`d_A z^p = (-1)^m z^(p+1) d_E`. Descending lifts occur locally over finitely many
p; at p = M-m cycles in A^M vanish since A^(M-1) is zero. The docstring already
records this endpoint explicitly. Source places and blueprint markers are present;
there are no definitions in the delivery, and the sole theorem proof is `sorry`.
There are no new nodes, dependency replacement modules, or corrected-statement citers.

Independent searches, using different terms from the first reading:

- msearch.py leanfinder: `internal Hom of a complex of finite locally free modules
  preserves exactness for a bounded below exact complex`: eight hits, about localization,
  Ext exact sequences and degreewise exactness, none stating this sheaf-Hom lemma.
- msearch.py loogle: `HomologicalComplex.Acyclic, ModuleCat`: zero hits.
- msearch.py grep: `hom.*(exact|acyclic)|((exact|acyclic).*hom)` in
  `Algebra/Category/ModuleCat/Sheaf`: nine incidental proof-text hits, no theorem match.
- msearch.py leansearch: `exact sheaf Hom complex finite rank free bounded above source
  bounded below acyclic target`: service returned Internal Server Error; unavailable,
  with no mathematical verdict assigned.
- Independently searched all upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json for `homcomplex|hom_complex|hom.*acyclic|acyclic.*hom`.
  Opened upstream `WeilConjectures.Algebra.Homology.InternalHom`: its monoidal internal
  Hom uses a different sign convention and supplies a tensor-Hom adjunction, not this
  acyclicity theorem. Existing exact-functor preservation of acyclicity likewise has
  a different construction and hypotheses. The project's `finiteFreeInternalHomExact`
  concerns a short exact sequence and is a proof input, not the present statement.
  No existing exact match or declaration-name collision was found.

Validation: checked programmatically that `lean.statement` equals the complete theorem
signature verbatim, and every Lean line has length at most 100. Independently ran
scompile.py on the unchanged module: exit code 0, 1.5 seconds, no errors or warnings.
