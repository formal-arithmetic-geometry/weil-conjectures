## Worker report

The module Sheaf.Paper.FiniteImmersionConstructibilityInterval states
AlgebraicGeometry.Scheme.finiteImmersion_constructibility_interval. Its only postponed
proof is the theorem of this item. Four fully written Prop-valued helper definitions
name its clauses; they construct no mathematical object by choice or by sorry.
The seven Q54 proof steps, the statement, and the reviewed split are retained verbatim.
The docstring carries all seven proof steps for the future prover.

Hypotheses and coefficients, checked against the node and its source:

- The fixed global finite-field tuple is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  The prime and its distinction from characteristic are `l`, `[Fact l.Prime]`,
  and `_hl : l ≠ D.p`. No morphism from X to the finite field is added: the node does
  not assume one.
- The finite coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  `n : ℕ` and `hn : 1 ≤ n` give exactly the positive integer levels.
  Every operation uses `Padic.coefficientExtensionRing l E n`, the dependency's
  quotient by the nth power of its chosen uniformizer in its valuation ring.
  The recorded intrinsic constructibility predicate supplies the existing finiteness
  proof for this ring internally; no extra finite-ring hypothesis is imposed.
- X is a scheme with `[IsLocallyNoetherian X] [CompactSpace X]`, exactly locally
  Noetherian and quasi-compact. `_hX : IsUnit (l : Γ(X, ⊤))` means l is invertible on
  X. This is equivalent to invertibility in every local ring: the local inverses
  are unique and glue to a global inverse. Z and U are arbitrary schemes of the
  same universe, with no reducedness assumption.
- `i : Z ⟶ X` and `[IsClosedImmersion i]` give the closed immersion; `j : U ⟶ X`
  and `[IsOpenImmersion j]` give the open immersion. The equation
  `_hU : Set.range j = (Set.range i)ᶜ` expresses the complementary open. No extra
  quasi-compactness hypothesis is added: Noetherianity supplies it.

Each conclusion clause has the following Lean rendering:

- `sfFiniteImmersionAction` is applied to the two recorded canonical constant-ring
  inverse images `proEtaleConstantRingPullback` and their exact termwise derived
  functors `proEtaleConstantRingDerivedPullback`, for i and j, and to the sectionwise
  `proEtaleConstantModuleDirectImage i` with its genuine unbounded K-injective
  `proEtaleConstantDerivedDirectImage i`.
- In each action, `PreservesFiniteLimits F ∧ PreservesFiniteColimits F` is ordinary
  exactness. `DF.IsTriangulated` gives triangulated exactness. The natural
  isomorphism `DerivedCategory.Q ⋙ DF ≅ F.mapHomologicalComplex ... ⋙ DerivedCategory.Q`
  states that these are termwise operations, including Ri_*=i_* on arbitrary
  representatives and morphisms. This is an isomorphism of derived functors, in
  addition to the required cohomology statement; it is not merely degreewise data.
- The natural isomorphism for every `r : ℤ`,
  `DF ⋙ DerivedCategory.homologyFunctor ... r ≅
  DerivedCategory.homologyFunctor ... r ⋙ F`, states H^r(FC) ≅ F H^r(C), naturally
  in C. `Nonempty` expresses existence of that natural isomorphism, not a choice
  of an arbitrary functor or a replacement operation.
- The predicates P and Q in all three actions are exactly the dependency's
  `intrinsicFiniteTorsionConstructible l E n hn` on the source and target scheme.
  `∀ C, P C → Q (DF.obj C)` says the canonical ambient functor maps the full bounded
  constructible subcategory into the specified full subcategory. Together with
  ambient triangulated exactness this is precisely its induced exact triangulated
  functor on D^b_c; it adds no resolution or bounded-constructible-term assumption.
- `∀ (a b : ℤ) C, proEtaleCohomologicalSupport C ⊆ Set.Icc a b →
  proEtaleCohomologicalSupport (DF.obj C) ⊆ Set.Icc a b` preserves exactly the same
  closed integer interval. The definition of support and the homology functor are
  the recorded dependency declarations, without a private substitute.
- `sfFiniteImmersionStratum A s M` names just local constancy and finiteness of every
  geometric module stalk for the restriction of M along the supplied immersion s.
  These are exactly the two restriction clauses in the existing
  `IsConstructibleProEtaleModuleSheaf`, which is used by intrinsic constructibility.
  The helper does not redefine constructibility or local constancy.
- `sfFiniteImmersionPullbackPartitions A i` and the same expression for j quantify
  over every supplied `S : Stratification X` satisfying those restriction clauses.
  They assert the same clauses for `S.pullback i` and `S.pullback j`. The existing
  Stratification stores constructibility, local closedness, disjointness, covering,
  the schemes of the strata and their immersions. Its actual pullback keeps the
  index set and has domain `pullback (S.immersion ν) g` and immersion `pullback.snd`.
  Thus these are exactly the asserted fibre-product partitions, not unspecified
  alternative witnesses or reductions of the strata.
- `sfFiniteImmersionClosedPartitions A i j` quantifies over every supplied closed-side
  sheaf N and partition S. It supplies a stratification T indexed bijectively by
  `Fin S.n ⊕ Unit`. The inl strata are isomorphic over X to the same original
  S.domain μ with composite immersion `S.immersion μ ≫ i`. The inr stratum is
  isomorphic over X to exactly U with j. Every T restriction satisfies the
  local-constancy/finite-stalk condition for the ordinary closed direct image.
  Finally the restriction along each original composite is isomorphic to the
  original restriction of N, and restriction along j is `IsZero`.

Dependency declarations read and reused:

- def-weil-finite-field-fiber: Sheaf.Paper.FiniteFieldFiber,
  WeilConjectures.FiniteFieldDatum (reexported by the constructibility module).
- def-weil-l-adic-coefficient-extension:
  Sheaf.NumberTheory.Padics.CoefficientExtensionFinite,
  Padic.finite_coefficientExtensionRing; its imported CoefficientExtension module
  gives coefficientExtensionRing, integers and chosen uniformizer.
- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  AlgebraicGeometry.IsLocallyNoetherian. Also CompactSpace supplies quasi-compactness.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  AlgebraicGeometry.IsClosedImmersion; def-weil-open-immersion:
  Mathlib.AlgebraicGeometry.OpenImmersion, AlgebraicGeometry.IsOpenImmersion.
  Both are publicly reexported by the statement imports.
- def-weil-pbc-proetale-site: Mathlib.AlgebraicGeometry.Sites.Proetale,
  AlgebraicGeometry.Scheme.ProEt and ProEt.topology; the existing
  Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory.proEtaleDerivedCategory
  specializes the module derived category on exactly that site.
- def-weil-pbc-constant-sheaf: Mathlib.CategoryTheory.Sites.ConstantSheaf,
  CategoryTheory.constantSheaf, used by the existing proEtaleConstantRing.
- def-weil-finite-torsion-constructibility:
  Sheaf.Paper.IntrinsicFiniteTorsionConstructibility,
  AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible. This uses the
  identical recorded quotient coefficients and cohomological predicate with the
  mathematically unused global datum suppressed internally, as its record specifies.
- def-weil-pbc-proetale-operations:
  Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations,
  proEtaleConstantRingPullback and proEtaleConstantRingDerivedPullback;
  its imports reexport proEtaleConstantModuleDirectImage and
  proEtaleConstantDerivedDirectImage. These retain the canonical constant-section
  coefficient maps and the genuine K-injective construction of right direct image.
- lem-weil-pbc-proetale-ringed-open-closed:
  Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed, proEtale_ringed_open_closed,
  publicly imported as a stated dependency and proof input. Its specialized use
  supplies exactness and the closed counit and open-zero identities.
- def-weil-derived-cohomology-sheaves:
  Mathlib.Algebra.Homology.DerivedCategory.HomologySequence,
  DerivedCategory.homologyFunctor and homologyFunctorFactors, reexported by the
  statement imports.
- def-weil-cohomological-support:
  Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport,
  AlgebraicGeometry.Scheme.proEtaleCohomologicalSupport.
- lemma-constructible-pullback-stratification:
  WeilConjectures.ConstructibleSheaf.Pullback,
  AlgebraicGeometry.Scheme.Stratification.pullback. This landed node is added to
  stmt_deps, since the signature uses its construction directly.

The stated proof dependencies with modules are imported as ordinary proof imports,
except those already public statement imports. These include the fixed-module
constructibility interface, finite-local-constancy pullback, exactFunctor_derivedFunctor,
siteInverseImage_tensor, immersion limit preservation and the finite constant-ring
comparison. Generic Mathlib leaf proof inputs (constructible/local-closed sets,
Noetherian opens, exact derived factorization and immersion composition) are already
reexported by the relevant statement imports; no unstated helper is postulated.

Edge cases: U empty, Z empty, X empty, N or M zero, empty strata in a nonempty finite
index set, or even a zero-index partition of an empty scheme are all accepted. The
pullback keeps all original indices, and the closed partition adjoins one U stratum;
retaining an empty member is allowed, and empty members can be discarded afterward.
The existing positive-number-of-strata constructibility convention is harmless on
an empty scheme (one empty stratum). No nilpotents are removed, as the over-X domain
isomorphisms expressly preserve scheme structures. n=1 is included; n=0 is excluded
exactly as in the node. No order a ≤ b is imposed: for a>b the support is empty and
exactness preserves the zero complex. Scheme and stalk universes are those of the
published site, with the module-value lift u+1; no universe equality is added.

Searches actually made with msearch.py:

- leanfinder, "Closed immersion pushforward and open and closed inverse image preserve
  constructible proetale module sheaves and cohomological intervals": eight hits,
  including scheme-module pushforward full/faithful and restriction; no complete match.
- loogle, '"constructible"': twelve constructible-subset hits, no such sheaf/derived
  theorem.
- grep, 'constructib.*(pushforward|immersion)|(pushforward|immersion).*constructib':
  zero Mathlib hits.
- leansearch, "Open and closed inverse image and closed direct image preserve
  constructible proetale module sheaves and every cohomological interval": eight hits
  on topological presheaves, constructible-set preimages and scheme restriction;
  none asserts this node.
- rg of the exact node id and the immersion/constructibility keywords in
  lean/WeilConjectures and lean/Sheaf found related etale, finite-Tor and condensed
  results, but none simultaneously states all these ordinary finite-stage operations,
  the prescribed actual partitions, and unchanged intervals. In particular the
  LocalizationFiniteTor theorem has an additional finite-Tor setting and does not
  assert these partition clauses. The existing Stratification.pullback and existing
  constructibility/stalk definitions were reused.

Sources opened: the exact main-20261015 finite-stage proof paragraph in the node's
source, Stacks proetale.tex lemma-closed-immersion (09AA),
lemma-closed-immersion-complement-retrocompact-exact (09BM),
lemma-ses-associated-to-open (09AH), sites-modules.tex lemma-pullback-locally-constant
(093R), and derived.tex lemma-right-derived-exact-functor (015F). No statement fault
or disputed assertion was found, and there is no statement correction or new node.

Validation: scompile.py compiled both its sandbox and library module views cleanly;
all variables and universes are explicitly bound and autoImplicit is disabled.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
