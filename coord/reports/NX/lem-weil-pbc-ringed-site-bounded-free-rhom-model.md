## Worker report

The module `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel` states
`CategoryTheory.ringedSite_boundedFree_rhom_model`; its only proof is `sorry`.
No definitions or nodes are added, and the natural-language statement is unchanged.

Hypotheses and clauses, checked against Tag 08JI in
`literature/stacks-project/sites-cohomology.tex`, lemma-Rhom-complex-of-direct-summands-finite-free:

- The small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
  This uses the Grothendieck topology associated to site coverings; the Hom calculation
  needs only its sheaf category. The explicit universe `u` is shared by the small site,
  coefficient rings and module carriers, as in the recorded derived-internal-Hom interface.
  Any site smaller than the module universe can be enlarged to that universe.
- The sheaf of commutative rings is `(R : Sheaf J CommRingCat.{u})`.
- Its module category is the dependency's transparent abbreviation
  `ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)`.
  `HasDerivedCategory.{w}` is the explicit localization/size convention, with morphism
  universe `w` bound explicitly, rather than an extra geometric assumption.
- `P N : CochainComplex ... ℤ` are exactly the two cochain complexes.
- `(a b : ℤ)`, `hP : ∀ i, b < i → IsZero (P.X i)` and
  `hN : ∀ j, j < a → IsZero (N.X j)` render the termwise bounds, not merely
  cohomological bounds. Bounds are explicit parameters; the theorem applies to any
  witnesses for the node's existential bounds.
- `hfinite` gives for each degree a natural number `r` and maps `s : P.X i ⟶ free ...`
  and `t : free ... ⟶ P.X i` with `s ≫ t = 𝟙 _`. A retract of a finite free object
  is precisely an object isomorphic to a direct summand in this abelian category.
  `ULift.{u} (Fin r)` supplies the finite basis in the coefficient universe; it does
  not require the module sheaf to be projective for global Hom.
- The first conclusion is the derived isomorphism between `Q.obj (homComplex P N)`
  and `(derivedInternalHom J R).obj (op (Q.obj P), Q.obj N)`.
- Canonicity is recorded by the second conjunct: for every K-injective replacement
  `α : N ⟶ I`, the *actual* Hom map induced by `α` becomes an isomorphism after `Q`.
  The recorded `derivedInternalHom_obj_iso` identifies the latter Hom complex with
  derived internal Hom, so this pins the assertion to resolution comparison instead
  of only asserting an unrelated isomorphism. Universal quantification over replacement
  maps is a conclusion, not an extra assumption on the supplied complexes.
- The existential `π n p q hpq` is a single family of product projections for the
  existing Hom complex. Its `Fan.mk` is limiting in every degree. This specifies
  the component-family interpretation independently of private implementation names.
- The differential clause, for `n + 1 = m`, is literally postcomposition by `N.d`
  minus `n.negOnePow` times precomposition by `P.d`. Auxiliary degrees and equalities
  align the indices without hidden transports; they force `p' = p+1`.
- The last clause gives injections `ι` into that same Hom-complex term indexed by
  `↥(Finset.Icc (a-n) b)`. `IsColimit (Cofan.mk ... ι)` is exactly the finite direct
  sum universal property. Its composites with the preceding product projections are
  identity for the matching integer and zero otherwise (`eqToHom` accounts only for
  equality of the index). Thus it asserts the canonical finite-diagonal description,
  rather than an arbitrary isomorphism to some unrelated finite sum. This avoids
  needing any additional finite-biproduct instance as a hypothesis.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for Mathlib `SheafOfModules` (the abelian instance is inherited).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` and its term/differential
  fields, exposed through the Hom-complex module.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`, and the full product/differential specification
  `homComplex_exists`. No private projection or new Hom complex is introduced.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`
  and its comparison/representative isomorphism statements.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, `homObjMap`, the existing sheaf-valued internal Hom.
- `def-weil-pbc-sites-and-cohomology` uses Mathlib's site and sheaf interfaces;
  its cohomology functors are not needed in the signature. The size-convention node
  has no declaration and is rendered by explicit universes and localization instance.
- Every recorded proof-dependency module is imported, including the Grothendieck/
  injective resolution statements, double-complex total, first-quadrant comparison,
  and quasi-isomorphism of Hom-complex maps. Mathlib leaves are imported from
  GrothendieckCategory.EnoughInjectives, DerivabilityStructureInjectives and
  DerivedCategory.KInjective. These imports preserve the node's proof plan.

Edge cases checked: rank zero is allowed (`r : ℕ`); a zero term is a retract of the
zero free sheaf. No lower bound on P or upper bound on N is assumed. If `a-n > b`,
the finite index type is empty, and the colimit condition says the term is zero.
There is no condition `a ≤ b`. All integer degrees, including negative degrees,
are permitted. `Int.negOnePow` gives the correct sign in all characteristics,
including characteristic two. Empty sites and zero coefficient rings are allowed.

Searches for an existing declaration:

- `msearch.py ... leanfinder`: “Derived internal Hom of bounded above finite projective
  sheaf complex into bounded below complex is computed by ordinary sheaf Hom complex”.
  Eight hits: sheaf cohomology, external K-projective Hom, Ext, projective resolutions;
  none states the internal sheaf Hom model on arbitrary ringed sites.
- `msearch.py ... loogle`: `"SheafOfModules", "homObj"`. One hit, the module structure
  on presheaf sections; no model theorem.
- `msearch.py ... grep`: `RHom|derivedInternalHom|bounded.*[Hh]om`, under
  `Algebra/Homology`. Twenty-five hits, predominantly external Hom, bounded homotopy
  categories and bifunctors; none is the sought internal sheaf Hom model.
- `rg` over the upstream WeilConjectures tree and project `lean/Sheaf`, using
  `bounded.*[Ff]ree.*[Hh]om|bounded.*[Pp]rojective.*[Hh]om` and the node ID.
  Read `DerivedHomFiniteFreeModel.lean` and its auxiliary module: they apply to
  ringed spaces with free terms, not arbitrary sites and summands. The other hits
  are ring-module or scheme specializations and applications. No exact match.
- Name-collision `rg` for `ringedSite_boundedFree_rhom_model` and
  `boundedFree_rhom_model` in Mathlib, upstream and project sources: no hit.
  The upstream name table was also checked for the dependency node IDs.

No statement correction or disputed mathematical assertion.

Repair of the earlier sandbox attempt: explicitly supplied `(R := R)` to both
`homObjMap` terms to prevent the precomposition term from inferring the site
and module universes as zero. Removed the unexplained heartbeat override;
no mathematical signature or node statement was changed by these repairs.
The node record was regenerated from the full current theorem signature.


## Second reading by NX

Read independently against the sandbox node, Stacks `sites-cohomology.tex`
Tag 08JI (lines 11959–12021), the surrounding internal-Hom section 08J7,
and the Hom-complex definition in Section 0A8X. The source assumes an arbitrary
ringed site; there is no hidden Noetherian, field, characteristic, or projectivity
hypothesis. The node specializes coefficients to commutative rings, consistently
with its recorded internal-Hom interface.

Object/hypothesis/conclusion inventory and matching:

1. Small ringed site `(C,O)`: `{C : Type u} [SmallCategory C]`,
   `J : GrothendieckTopology C`, and `R : Sheaf J CommRingCat.{u}`. Pass.
   Passing from the covering-site presentation of the sites dependency to its
   associated Grothendieck topology preserves the category of sheaves. The theorem
   uses only that category, and imposes no new condition on coverings.
2. Category of O-modules: `ringedSiteModules.{u}` applied to the ring sheaf
   obtained by `sheafCompose ... (forget₂ CommRingCat RingCat)`. Pass.
   Opened `RingedSiteModules.lean`: this is transparently `SheafOfModules`,
   not scheme modules or a privately constructed category. The coefficient
   forgetful functor drops commutativity structure without changing the ring.
3. Cochain complexes `P,N`: `P N : CochainComplex ... ℤ`. Pass: all integer
   degrees and actual module-sheaf differentials, using the recorded Mathlib notion.
4. Integers witnessing the bounds: `(a b : ℤ)`,
   `hP : ∀ i, b < i → IsZero (P.X i)` and
   `hN : ∀ j, j < a → IsZero (N.X j)`. Pass. These are termwise bounds,
   not weaker cohomology bounds. Quantifying over each witness gives the same
   theorem as applying it after eliminating the node's existential bounds.
5. Each `P^i` is a summand of a finite free sheaf: `hfinite` supplies `r : ℕ`
   and maps `s,t` with `s ≫ t = 𝟙 (P.X i)`. Pass. In an abelian category a
   retract is a direct summand, including a sheaf merely isomorphic to a summand.
   Opened Mathlib `Sheaf.Free`: `free I` is the coproduct of copies of `unit R`.
   `ULift.{u} (Fin r)` is a finite basis, not an assumption of global projectivity.
6. Derived category and localization: `[HasDerivedCategory.{w} ...]`,
   `DerivedCategory.Q`. Pass. Read the recorded localization signature; `w`
   is explicitly bound and expresses the project's localization size convention.
7. Derived internal Hom represented by the ordinary Hom complex: first conjunct
   `Nonempty (Q.obj (homComplex P N) ≅ (derivedInternalHom J R).obj
   (op (Q.obj P), Q.obj N))`. Pass. Opened `DerivedInternalHom.lean`:
   its definition really localizes the sheaf Hom bifunctor after functorial
   K-injective replacement, with the required contravariance and covariance.
8. Canonical resolution comparison: second conjunct asserts `IsIso` of
   `Q.map (((homComplexFunctor ...).obj (op P)).map α)` for every quasi-isomorphic
   K-injective replacement `α : N ⟶ I`. Pass: this specifies the actual comparison
   induced by α, rather than only existence of an unrelated derived isomorphism.
   It adds no hypothesis on P or N. Even when I is unbounded below, compare it
   with a bounded-below injective replacement J: K-injective localization
   bijectivity produces J → I commuting with the replacement maps up to homotopy.
   The recorded `quasiIso_homComplex_map` applies between these K-injective targets;
   Hom preserves target homotopies. Thus the universal replacement clause follows
   from the source model and is not an unjustified strengthening.
9. Degree-n term is the finite direct sum over `a-n ≤ i ≤ b`: `∃ π` gives
   product projections for `homComplex P N`; `∀ n, ∃ ι` supplies a colimiting
   `Cofan` indexed by `↥(Finset.Icc (a - n) b)`. Pass. The diagonal equations
   `ι i ≫ π ... = if h : (i : ℤ) = p then eqToHom ... else 0` make these
   injections and projections compatible. This is the stated finite diagonal,
   not an arbitrary sum isomorphism. Product and coproduct witnesses are
   conclusions and require no additional finite-biproduct hypothesis.
10. Differential `d_N f - (-1)^n f d_P`: the equation after projection π uses
    `homObjMap (𝟙 _) (N.d q' q)` minus `n.negOnePow` times
    `homObjMap (P.d p p') (𝟙 _)`. Pass. From `n+1=m`, `p+m=q`,
    `p+n=q'`, `p'+n=q`, one gets `q'=q-1` and `p'=p+1`, exactly the
    postcomposition and precomposition components in Section 0A8X.
11. Internal sheaf Hom: `SheafOfModules.homObj`, `homObjMap`. Pass.
    Opened the upstream declaration: it uses Hom on the localized site over each
    object, with the sheaf condition, not the group of global maps.

Universe and edge-case audit: `u,w` and every variable are bound. Site objects,
morphisms, rings and module carriers share the ambient smallness universe used by
`derivedInternalHom`; smaller sites/rings can inhabit that ambient universe by
cumulativity. There is no requirement that intrinsically different site universes
be equal: choose their common ambient bound, as the node's small-site convention
permits. There are no test-algebra quantifiers in a smaller independent universe.
The Hom output universe `max u u u` is u, so no hidden coefficient transport is
needed. Rank zero and zero terms are included; no `Nonempty` assumption on the
site or finite index occurs. If `a-n>b`, the empty cofan says the term is zero.
There is no assumption `a≤b`, no missing degree zero or negative degree, and no
upper bound on N or lower bound on P. Empty sites, hence empty-scheme instances,
and the zero ring are allowed. The integer sign works in characteristic two.

Independent searches: ran `msearch.py` LeanFinder with “Internal sheaf Hom from
finite locally free bounded above complexes preserves quasi-isomorphisms of bounded
below complexes” (eight hits: localization, sheaf cohomology, support and related
facts, no exact theorem); Loogle `"homObj", "homObjMap"` (zero hits); and grep
`finite.*[Pp]rojective|[Kk][Pp]rojective` (module and external K-projective results,
no ringed-site internal-Hom theorem). Searched upstream WeilConjectures and project
Sheaf/Homology by finite/projective/bounded/Hom/RHom concepts and searched Mathlib,
upstream and project for the proposed declaration name (no collision).
Opened `DerivedHomFiniteFreeModel.lean` and its auxiliary declaration: they are
restricted to ringed spaces and free terms, and do not supply this arbitrary-site
summand theorem. `StrictlyPerfectHomQuasiIso` is the bounded, ringed-space special
case; ring-module perfect Hom comparisons likewise do not match.

No new definition nodes or dependency modules were included, so H12/H13 review
introduces no further delivery items. All recorded statement dependencies were
read; HomComplex uses the real sheaf Hom product construction and the correct
bifunctor. The proof imports cover the node's existing dependency plan. The six
proof steps in the docstring reproduce the node's finite-free exactness, summand,
signed first-quadrant total, comparison, canonicity and finite-diagonal arguments.
There is one theorem with proof `sorry`, no definition or extra proof in this
module, no line exceeding 100 characters, and no unbound universe or variable.
The node's `lean.statement` was checked programmatically against the file and is
verbatim equal.

Mismatches found: none. Changed only this report by appending the independent
reading; retained the correct Lean and node record. No source-based statement
correction or citer audit was necessary. Server compilation via `scompile.py`
passed (11.3 seconds for the delivered module, nice 19, two threads, 60 seconds
per file); its side dependency RingedSiteModules also compiled successfully.
