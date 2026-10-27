## Worker report

The module Sheaf.Paper.ScalarModelRestrictionCriterion states
AlgebraicGeometry.ProEtale.scalarModelRestrictionCriterion with its whole proof
`sorry`. There are no new definitions, dependency repairs, or statement changes.
The source read is blueprint main-20261015,
sec-six-functors-basics/sk-lem-integral-models/sk-lem-integral-models-operations.proof.md,
paragraph (3); the five steps of the reviewed DAG proof are in the theorem docstring.

Hypotheses, clause by clause:

- The schemes T, X and Y have arbitrary common universe u; each has CompactSpace
  and QuasiSeparatedSpace, expressing exactly the stated qcqs hypotheses.
- h and k are scheme morphisms with IsImmersion instances. hdisjoint is disjointness
  of their set-theoretic ranges; hcover says that their union is the whole space.
- Λ is a sheaf of abelian groups on the coherent profinite site with MonObj and
  IsCommMonObj: the unbundled form of the general commutative condensed ring.
  condensedRingObj Λ W is the dependency's pulled-back coefficient ring R_W.
- M and H are Mathlib internal Mod objects over these rings. eh and ek are the
  supplied isomorphisms h*H ≅ M and k*H ≅ 0 in the module categories.
- S is the recorded Scheme.FiniteLocallyClosedStratification of X, which does not
  impose constructibility on the X-strata beyond the node's assumption.
- E is the assumed extended Scheme.Stratification of T, whose inherited fields
  require finite, disjoint, covering, locally closed, constructible images.
  hE_domain and hE_immersion identify its schemes and immersions with Y,k followed
  by S.domain a,S.immersion a ≫ h. HEq avoids transports along a separately chosen
  equality E.n = S.n + 1; equality of the dependent function types includes that
  indexing equality. Thus this is the specified extended stratification, with Y
  placed first, and it admits any scheme structures carried by the given immersions.
- C a is the given pro-etale cover of S.domain a. P a r is the fixed point module,
  with hP its finite presentation. As in HasFiniteConstantLocalModel, a finitely
  presented module over the condensed coefficient ring on the point represents
  exactly a finite matrix over Λ(*); pulling it from the point is scalar extension
  of the associated finitely presented Λ(*)-module. No arbitrary coefficient
  matrices over a scheme or replacement model modules are used.
- models is the supplied isomorphism v* s* M ≅ p_V* P, using exactly C and P.

Conclusions, clause by clause:

- The first conjunct gives the internal module isomorphisms (s_a ≫ h)*H ≅ s_a*M.
- The second gives v*(s_a ≫ h)*H ≅ p_V* (P a r), for the original C a and P a r.
- The third gives the rank-zero presentation, 0 ≅ cokernel of the zero map
  Mod.finiteFree Λ 0 ⟶ Mod.finiteFree Λ 0. This is the categorical presentation
  Λ(*)^0 → Λ(*)^0 → 0 → 0, not just an unspecified finite presentation.
- The fourth says that scalar extension of zero to Y is zero.
- The fifth gives the zero scalar-model isomorphism after pullback along 𝟙 Y,
  namely on the singleton identity pro-etale cover, with scalar module exactly 0.
- The sixth says that each restriction along the supplied E has a finite constant
  local model, so that E itself is adapted to H.
- The last is IsConstantModelConstructible Λ T H, the stated constructibility.

Dependency declarations read and used:

- The scheme-conventions node defines no new notion: qcqs is encoded by the above
  standard Mathlib classes, and immersions by AlgebraicGeometry.IsImmersion from
  Mathlib.AlgebraicGeometry.Morphisms.Immersion (the immersion clause of the
  recorded closed-immersion dependency, reexported by the stratification module).
- Sheaf.Topology.ProfiniteCondensedRing, Profinite.CondensedRing: its transparent
  Mon abbreviation is used in the equivalent unbundled form required by the
  constructibility and module-pullback interfaces. It is publicly imported.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic,
  AlgebraicGeometry.ProEtale.condensedRingObj and coefficientRing: these construct
  the pulled-back rings by upperStarFromPoint and its monoidal structure.
- Mathlib.CategoryTheory.Monoidal.Mod, CategoryTheory.Mod, ModObj and Mod.Hom:
  genuine internal module objects, with action-preserving morphisms.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs,
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar and upperStarComp:
  the recorded ringed-topos pullback and its composition isomorphism. upperStar
  is mapMod followed by extendScalars along condensedPullbackHom.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification,
  AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification: exactly the
  recorded stratification dependency without an extra constructibility condition.
- Mathlib.Topology.Constructible, Topology.IsConstructible: used through E's
  inherited isConstructible_stratum field; Scheme.Stratification's full signature
  and inherited Topology.Stratification fields were read in upstream sources.
- Sheaf.Paper.CondensedConstantConstructibility,
  AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel,
  IsFiniteConstantStratified and IsConstantModelConstructible: the exact recorded
  scalar-model notion, with its qcqs branch and affine-local branch.
- The proof-only dependencies are imported through
  Mathlib.CategoryTheory.Adjunction.CompositionIso (Adjunction.leftAdjointCompIso)
  and WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
  (Mod.extendScalars and extendRestrictAdjunction). All other proof dependencies
  are already public imports used by the statement.

Edge cases checked before writing: n = 0 leaves E with just the Y stratum and the
old-model assertions vacuous; Y empty still has its identity cover and zero model;
X or T empty is permitted; the zero coefficient ring is permitted; no reducedness,
Noetherian, separatedness, nonemptiness, or coefficient topology hypothesis was
added. Old strata can have any scheme structure allowed by their immersions.

Searches actually run:

- msearch.py leanfinder, query "Finite constant scalar models of a module sheaf
  transfer across restriction isomorphisms on an extended finite stratification":
  eight hits, including ModuleCat.Tilde.res_const, ModuleCat.Tilde.exists_const,
  sheaf finite-type generators and Condensed.finFree; none states this criterion.
- msearch.py loogle, query
  "CategoryTheory.Functor.mapIso, CategoryTheory.Mod.IsFinitelyPresented": no hits,
  with unknown identifier CategoryTheory.Mod.IsFinitelyPresented in Mathlib.
  The finite-presentation predicate was found and read in the project instead,
  WeilConjectures.CategoryTheory.ModuleObjects.Free.
- msearch.py grep, query
  "FiniteConstantLocalModel|ConstantModelConstructible|scalar.model.*restriction":
  zero Mathlib hits.
- rg on lean/WeilConjectures and lean/Sheaf for FiniteConstant, scalarModel,
  scalar_model and restriction_criterion found the existing constructibility
  definition and isomorphism-invariance helpers, but no criterion preserving
  specified covers and scalar modules on a complementary extended stratification.
- rg on both source roots and dag/lean_names_upstream.json for
  ScalarModelRestrictionCriterion, scalarModelRestrictionCriterion and
  scalar_model_restriction_criterion: no hits. grep -rn for the item id in
  lean/WeilConjectures: no hits.

Validation: scompile.py checked both the sandbox and the named library module
cleanly (2.3 seconds and 2.2 seconds). Auto-implicit variables are disabled and all
universes are explicit. The theorem's proof remains sorry, as required by stage 2.
The initial checks identified missing ZeroObject notation scope and missing
explicit Fin.cases motives; both were repaired without changing the mathematics.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
