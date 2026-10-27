## Worker report

The module `Sheaf.Paper.FinitePrincipalSupportUnitAssembly` states the assigned node as
`AlgebraicGeometry.ProEtale.CondensedRing.FinitePrincipalSupport.finite_principal_support_unit_assembly`.
Every theorem proof is `sorry`; the only postponed theorem is this assigned theorem.
The remaining declarations construct the objects and canonical maps needed to read it.
No new DAG nodes, dependency repairs or statement corrections are needed.

The previous dispatch failure confused Q38's accepted stage-1 split with a Lean statement
landing. The live node has a reviewed six-step split and no Lean record. This delivery
preserves that statement, proof, review and every non-`lean` field.

Hypotheses and objects, clause by clause:

- Arbitrary commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]`. This is the unbundled form of the
  recorded `Profinite.CondensedRing` abbreviation; no topological presentation or
  admissibility, finite coefficient, characteristic or torsion restriction is assumed.
- For every scheme, the coefficient is the imported `condensedRingObj Λ X`, which is
  literally `(upperStarFromPoint X).obj Λ`. The imported monoidal structure supplies
  its transported multiplication and unit. `supportModules Λ X` is exactly the
  recorded `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
- The affine base is `Spec (CommRingCat.of S)`, with `{S : Type u} [CommRing S]`.
  The binder `{r : ℕ}` permits r=0, and `f : Fin r → S` supplies precisely r elements.
  Every finite subset is `J : Finset (Fin r)`; there is no choice of an ordering in
  the vanishing assumption or the invertibility conclusion.
- `openSet f J = J.inf (fun b => PrimeSpectrum.basicOpen (f b))` is exactly
  D(product over J), by `PrimeSpectrum.basicOpen_mul` and D(1)=top. It introduces
  no alternate scheme notion. `openScheme f J` is this open subscheme, with the
  empty intersection represented by X itself. `inclusion f J` is its actual inclusion,
  using only equality transports and the Mathlib open inclusion. In particular
  `inclusion f ∅` is definitionally the identity.
- `step f J a` is the canonical inclusion for `insert a J`, built with
  `Scheme.homOfLE` and the finite-intersection inclusion. It is e_{J,a} in the node.
- `divisor f J a` is `pullback.snd` of Spec(S/(f_a)) over the inclusion of X_J.
  Thus its source has the complete scheme structure of V(f_a) on X_J, including
  nilpotents; it is neither an arbitrarily chosen closed immersion nor a reduced
  replacement. No additional parameters for these inclusions are assumed.
- The arbitrary unbounded complex is `K : DerivedCategory (supportModules Λ
  (Spec (.of S)))`. The restricted complex K_J is
  `(moduleObjectDerivedPullback Λ (inclusion f J)).obj K`, canonically ordinary
  restriction since the recorded module pullback is exact. No boundedness,
  constructibility, perfectness, local freeness or K-injectivity assumption on K occurs.
- `hvanish` quantifies over every J and every `a : Fin r`, with precisely `a ∉ J`.
  Its conclusion is `IsZero ((closedSupport Λ (divisor f J a) (step f J a)).
  rightDerivedFunctor.obj K_J)`. The imported `closedSupport` is the exact dependency
  construction `supportKernel Λ j ⋙ supportPullback Λ i`, with the kernel of the
  specified ordinary open adjunction unit. This is the requested R underline Gamma.

Conclusions, clause by clause:

- The first conjunct is `∀ J, IsIso ((derivedUpperStarLowerStarAdjunction Λ
  (inclusion f J)).unit.app K)`. It asserts invertibility of the actual specified
  adjunction unit on every subset, not existence of some isomorphism of objects.
- `pullbackComparison` is the recorded `leftDerivedUpperStarComp`, preceded by the
  equality transport identifying the composite open inclusion. `pushforwardComparison`
  is `conjugateIsoEquiv` applied to its inverse and the specified composite adjunction.
  It therefore has exactly the stipulated direction R i_{J+a,*} -> R i_{J,*} R e_*.
- `unitTargetComparison` applies that comparison at the restricted complex and maps
  the canonical pullback comparison by the composite right adjoint. This explicitly
  accounts for the target identification implicit in the node's displayed equality.
  The second conjunct states `eta_{J+a} ≫ unitTargetComparison.hom = eta_J ≫
  R(i_J).map (eta_e at K_J)` for every missing a, which is that displayed equality
  in Lean's diagrammatic composition order.
- `emptyPullbackComparison` is the recorded canonical `leftDerivedUpperStarId`.
  `emptyPushforwardComparison` is its inverse's conjugate against the identity
  adjunction. `emptyTargetComparison` combines these comparisons. The third conjunct
  says that the empty-set actual unit followed by this canonical comparison is `𝟙 K`.
- `assembledUnit` recursively composes the preceding assembled unit, the pushed
  step unit and the inverse of `unitTargetComparison`. Its base is the specified
  empty-set unit. The final conjunct quantifies over every `l : List (Fin r)` with
  `l.Nodup`, and identifies its assembled map with the one actual unit at `l.toFinset`.
  Thus every ordering of any finite set yields the same specified unit. Equality
  of two orderings is through these canonical target comparisons, not a bare
  nonempty isomorphism or an arbitrary family of comparison arrows.

Every variable and universe is explicitly bound, with `set_option autoImplicit false`.
The site is `Scheme.ProEt.topology` and abelian coefficients use universe u+1, exactly
as the recorded pro-etale framework. No extra universe equality is imposed. The
statement is in the derived category throughout, not merely on cohomology sheaves.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, the bundled
  form of the unbundled arbitrary ring-object input used here.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `upperStarFromPoint`, `coefficientRing`, `condensedRingObj`, and its commutativity
  instance. Their definitions transport the actual tensor ring structure.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`, `Mod.Hom`, the existing
  category and compatible module maps. No replacement module category is defined.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPullback` and
  `moduleObjectDerivedPushforward`, transparent names for total derivation of the full
  module-object functors. Its upstream import provides
  `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarComp`.
- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`: `supportModules`,
  `closedSupport` and its additivity instance. Its definition and docstring give the
  exact kernel-then-closed-inverse-image functor in the assumption; `closedSupport_triangle`
  supplies the planned proof's localization triangle. Its alternative scalar-transport
  presentation of inverse image does not replace the specified derived adjunction used
  in this delivery's unit statements.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence`:
  `leftDerivedUpperStarId`, obtained by deriving the canonical underived identity
  comparison. This additional canonical identity helper is already upstream.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`, with exactly
  `(L₂ ≅ L₁) ≃ (R₁ ≅ R₂)`, and `Mathlib.CategoryTheory.Adjunction.Basic`:
  `Adjunction.comp`, `Adjunction.id`. Their signatures fix every direction here.
- `Mathlib.AlgebraicGeometry.Restrict`: actual `Scheme.Opens.ι` and `Scheme.homOfLE`.
- Proof-only imports include `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
  for `module_pullback_additive_exact`, and
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` for the zero-cone criterion.
  The other recorded proof modules are already public imports or transitive imports.

Source and proof: I read `literature/stacks-project/sites-cohomology.tex`,
`lemma-derived-pushforward-composition` (0D6E), where the comparison is obtained by
uniqueness of right adjoints to canonical pullback composition. The six-step
finite-support assembly is the node's agent argument; it is not attributed verbatim
 to Stacks. Its full natural-language proof appears in the theorem docstring,
including exactness, support triangle, conjugate normalization, empty identity,
finite-subset induction and independence of ordering.

Edge cases checked before stating: r=0 leaves only the empty set and empty list,
with a vacuous support hypothesis and the canonical identity unit. The zero ring
permits empty X. Zero K is allowed in the ordinary derived category. Unit f_a has
empty divisor; zero or nilpotent f_a has empty principal open, and the support
vanishing forces K_J=0, so the proposed unit to zero is correctly invertible.
Repeated values among different f_a are permitted. Empty closed subschemes,
nonreduced closed divisors, arbitrary positive or zero characteristic, and zero
coefficients impose no extra assumptions. Repeated list indices are defined by the
helper but the theorem asserts the node's ordering clause only for distinct indices.

Searches made:

- `msearch.py leanfinder`, query "Vanishing derived sections with support on successive
  principal complements makes the specified derived open adjunction unit invertible":
  eight hits, concerning ordinary basic opens and localization of sections. Names include
  `RingedSpace.isUnit_res_basicOpen`, `exists_of_res_zero_of_qcqs`,
  `Scheme.zero_of_zero_cover`; none states this unbounded condensed-module assembly.
- `msearch.py loogle`, query "CategoryTheory.Adjunction.comp,
  AlgebraicGeometry.Scheme.basicOpen": zero hits.
- `msearch.py grep`, query `(localCohomology|localizationTriangle|sectionsWithSupport).
  *(unit|IsIso)|unit.*(localCohomology|sectionsWithSupport)` (one regular expression
  without the line break): zero hits.
- `msearch.py grep`, query `basicOpen.*(prod|inf)|basicOpenLE|basicOpen.*top`,
  in AlgebraicGeometry: 25 hits, providing existing open-restriction operations,
  not the assigned statement. Further grep for closed complements, zero loci and
  open inclusions found the existing scheme machinery.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node identifier and for
  `principal.*support.*unit|finitePrincipalSupport|finite_principal_support|finitePrincipal`:
  no existing statement. Neighboring root-tower modules use particular coefficients
  and root algebras; no exact general finite-principal support assembly is present.
- I also searched and read the upstream and Mathlib definitions of derived adjunctions,
  canonical pullback composition, the identity comparison, module objects, small
  pro-etale sites, finite intersections of basic opens, and quotient spectra.

No STATEMENT-DISPUTED issue remains. There is no source-based statement correction.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
