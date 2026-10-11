## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProjGradedModuleSheafExists.lean` states
`AlgebraicGeometry.Proj.gradedModuleSheaf_exists`, with its sole theorem proof `sorry`.
It includes a fully implemented local scalar-restriction instance, using `Module.compHom`
and Mathlib's algebra map from homogeneous localization to ordinary localization.
There are no new mathematical definitions, new nodes, dependency modules, or statement
corrections. The item's statement and proof fields are unchanged. Its `stmt_deps` gains
the already landed `def-sc-degree-zero-module-fractions`, whose declaration is used
for both chart modules and prime-localized modules. This is the standing
STMT_DEPS MAY GAIN LANDED NODES rule of `coord/brief-stage2.md` §5.

Source checked: Stacks Project, Constructions, Section 01M3 at
https://stacks.math.columbia.edu/tag/01M3 (the local literature checkout is absent),
including Lemma 01M4, the construction before Definition 01M6, Lemma 01M7, and
Lemma 01MB. This is a supporting node, not the blueprint unit's own statement.
The theorem docstring carries all eight proof steps of the node, including the
basis construction, coefficient identification by germs, finite standard covers,
module localization exactness, basis extension and uniqueness, quasi-coherence,
stalks, and global-section gluing.

Hypotheses and introduced objects:

- The commutative ring is `{S : Type u} [CommRing S]`; its nonnegative grading is
  `(𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]`. `Proj 𝒜` is the dependency's existing
  Mathlib scheme. No field, Noetherian, finite-generation, or degree-one-generation
  assumption is imposed.
- The module is `{M : Type u} [AddCommGroup M] [Module S M]`. Its integer grading is
  `𝓜 : ℤ → AddSubgroup M`, with `h𝓜 : DirectSum.IsInternal 𝓜`, and `hsmul` states
  `S_n • M_z ⊆ M_(n+z)` for every natural `n` and integer `z`. Thus negative graded
  components are permitted even though chart fractions have nonnegative numerator
  degree. All variables and the universe are explicitly declared. The common universe
  is arbitrary; no countability or finite-dimensionality condition occurs.
- Local notation `Fidx` is the subtype of pairs `(f,d)` with `0 < d` and `f ∈ 𝒜 d`.
  It includes zero and nilpotent homogeneous elements. `D[f]` expands to
  `Proj.basicOpen 𝒜 f.val.1`, `R[f]` to `HomogeneousLocalization.Away 𝒜 f.val.1`, and
  `N[f]` to `LocalizedModule.Away f.val.1 M`. These are notation, not copied definitions.
- `Z f : Submodule R[f] N[f]` is constrained to have exactly the carrier
  `LocalizedModule.degreeZeroFractions (fun n ↦ 𝒜 n) (fun n ↦ 𝓜 n) (powers f)`.
  Scalar action comes from ordinary module localization via the homogeneous ring's
  inclusion. A fraction with denominator `f^m` has degree-zero numerator of degree
  `m*d`, by the graded-ring decomposition, except that a zero denominator makes the
  localization zero. Thus this gives precisely the node's `M_(f)`, with the ordinary
  localization relation, rather than an unconstrained chart module.
- The structure-sheaf chart ring map is the existing `Proj.awayToSection 𝒜 f.val.1`.
  Its isomorphism for positive homogeneous `f` is Mathlib's `basicOpenIsoAway`.

Clause (a):

- `D[g] ≤ D[f]` is the standard-open inclusion. The conclusion explicitly gives
  `∃ e k a, 0 < e ∧ a ∈ 𝒜 k ∧ g^e = a*f`.
- `rho f g i : Z f →+ Z g` is a well-defined additive map. `rhoS f g i` is a ring map
  `R[f] →+* R[g]`. The explicit equation
  `rho ... (r • q) = rhoS ... r • rho ... q` is linearity after restriction of scalars.
  Later the ring map is pinned to the structure-sheaf restriction using `awayToSection`.
- For EVERY `e,k,a` satisfying the relation, and EVERY representative `q = y/f^m`,
  the coerced value in `N[g]` is `mk (a^m • y) (g^(e*m))`. The map is indexed by
  open inclusion alone, never by a choice of relation witnesses. This states both
  the fraction formula and independence of those witnesses. Representatives are
  elements of Mathlib's ordinary quotient localization, so well-definedness is built
  into the existence of this map and the formula's quantification over all representatives.
- The next conjuncts state `rho f f i q = q`,
  `rho g h j (rho f g i q) = rho f h (j.trans i) q`, and bijectivity whenever
  `D[f] = D[g]`. A bijective additive semilinear map, with coefficient rings identified
  by their chart section isomorphisms, is the required module isomorphism.

Clause (b):

- `F : SheafOfModules (moduleRings (Proj 𝒜).toRingedSpace)` is an actual sheaf of
  modules over the structure sheaf. `alpha f : F.val.obj (op D[f]) ≃+ Z f` gives
  each chart identification. Its scalar equation uses `awayToSection` explicitly,
  giving precisely an `S_(f)`-module identification. Equality of sections in the node
  is rendered as an identification, not literal equality of carriers.
- `alpha g (F.val.map (homOfLE i).op s) = rho ... (alpha f s)` states the restriction
  clause. The next ring equation identifies `rhoS` with the coefficient restriction.
- For ANY sheaf `G` and ANY additive chart identifications `beta` obeying the same
  scalar and restriction laws, there is `∃! phi : F ⟶ G, IsIso phi ∧ ...`. The last
  equation is `beta f (phi.val.app ... s) = alpha f s`. Thus uniqueness is exactly
  uniqueness compatible with the given identifications; it does not falsely assert
  that the sheaf has only one arbitrary automorphism. The morphism is a module-sheaf
  morphism, not just a morphism of underlying sets.

Clause (c):

- `F.IsQuasicoherent` is Mathlib's quasi-coherence predicate used by the recorded
  dependency `pqf-def-coherent`; its module explains equivalence to the affine-local
  tilde characterization on schemes. No separate coherence assumption is added.
- For each `x : Proj 𝒜`, `T[x]` is the prime-complement submonoid of
  `x.asHomogeneousIdeal.toIdeal`. `Rp[x]` is Mathlib's homogeneous localization there.
  `Zp x : Submodule Rp[x] (LocalizedModule T[x] M)` has exactly the existing
  `degreeZeroFractions` carrier: homogeneous numerator and denominator of equal
  natural degree, denominator outside the homogeneous prime. Although the ambient
  ordinary localization inverts all elements outside the prime, the carrier formula
  restricts denominators to homogeneous ones. Equality is unchanged: if a homogeneous
  relation is killed by a general element outside a homogeneous prime, one of its
  homogeneous components outside the prime kills it.
- `mu x` identifies `(RingedSpace.moduleStalkFunctor ... x).obj F` additively with
  `Zp x`; its scalar equation is semilinearity along Mathlib's `Proj.stalkIso 𝒜 x`.
  The additional germ formula fixes the canonical identification: the germ of a chart
  section corresponding to `y/f^m` maps to `mk y t`, for every `t` in the prime
  complement with underlying scalar `f^m`. This uses the recorded stalk carrier,
  not another definition of stalk. Such `t` exists whenever `x ∈ D[f]`.

Clause (d):

- `eta : 𝒜 0 →+* Γ(X,O_X)` is pinned on EVERY standard open to
  `awayToSection (fromZeroRingHom ... r)`. It is the canonical coefficient action.
- `gamma : 𝓜 0 →+ Γ(X,F)` is additive and its explicit scalar equation states
  `gamma (r • m) = eta r • gamma m`. The membership proof for the subtype `r • m`
  is the given graded scalar compatibility `hsmul 0 0`; no proof or data is hidden.
  This is the `S_0`-linear map, expressed without choosing a second module structure.
- For every `m` and `f`, the chart image of the restriction of `gamma m` is `mk m 1`.
  The following conjunct explicitly states compatibility under every `rho`.
- The final universally quantified implication says that any global section with
  those chart values equals `gamma m`. This gives existence and uniqueness of the
  global section for EACH degree-zero element, not surjectivity or injectivity of
  the global-section map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `AlgebraicGeometry.Proj`;
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`: `Proj.basicOpen`,
  `Proj.awayToSection`, `Proj.basicOpenIsoAway` (its identification is used semantically),
  and `Proj.stalkIso`.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization`, `HomogeneousLocalization.Away`,
  `HomogeneousLocalization.AtPrime` (the notation expands its definition),
  its inclusion algebra instance, and `HomogeneousLocalization.fromZeroRingHom`.
- `Sheaf.AlgebraicGeometry.Coherent`: the dependency's explanation identifying
  quasi-coherence with `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, `SheafOfModules.Hom`;
  `Mathlib.Algebra.Category.ModuleCat.Presheaf`: `PresheafOfModules.obj`, `map`,
  and `Hom.app`. The coefficient sheaf is `AlgebraicGeometry.moduleRings`, imported
  through the recorded coherent module.
- `Sheaf.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`; germs use
  `TopCat.Presheaf.germ` on the same underlying abelian-group presheaf.
- Added landed dependency `def-sc-degree-zero-module-fractions`:
  `Sheaf.Algebra.Module.DegreeZeroFractions`, `LocalizedModule.degreeZeroFractions`.
  Ordinary fractions and actions are `LocalizedModule.mk` and `Module.compHom`.

Edge cases checked before and during writing:

- Zero or nilpotent positive homogeneous denominators give the empty standard open
  and zero localized modules. They remain in `Fidx`; the formula and identifications
  are still meaningful, with no nonzero-denominator hypothesis.
- The zero ring and rings concentrated in degree zero have empty Proj. The positive
  standard-open family may be empty or consist of empty opens. The empty sheaf's
  global sections are zero, so all existence and uniqueness claims remain valid.
- Zero module, modules supported only in negative degrees, and `M_0 = 0` are allowed.
- Exponent `m = 0` is included in the fraction formula. In particular the formula
  sends `m/1` to `m/1`. There is no claim that `M_0 → Γ(X,F)` is an isomorphism.
- Positive degrees need not equal one. No characteristic restrictions occur.
- Repeated indices for the same element/open, including the zero element with more
  than one possible degree, cause no ambiguity: equality-of-open restrictions are
  isomorphisms, and the formula is independent of witnesses.

Node-proof observation: the written injectivity argument in proof step 7 says
`c^m x = 0` from `cx = 0`, which needs care when the displayed denominator exponent
is zero. The statement is true. The module docstring instead uses the correct
smaller-open germ argument: on `D_+(fc)`, both `f` and `c` are inverted, so a numerator
killed by `c` has zero germ, also for exponent zero. No statement correction is needed.

Searches actually performed (the msearch results are logged in `searches.jsonl`):

- `msearch.py leanfinder`: "sheaf of modules on Proj associated to a graded module
  with sections degree zero localization". Eight hits: the Proj structure sheaf,
  `Proj.awayToSection`, and its ring-section helpers. None handles an arbitrary module.
- `msearch.py loogle`: "HomogeneousLocalization.Away, Module". Zero hits.
- `msearch.py leansearch`: "degree zero homogeneous localization of a graded module".
  Service unavailable (Internal Server Error); no mathematical verdict drawn.
- `msearch.py grep`: "GradedModule|Gmodule|graded.*module|module.*graded" in
  `AlgebraicGeometry`. One hit, the open namespace in the structure-sheaf file.
- `msearch.py grep`: "HomogeneousLocalization.*Module|Module.*HomogeneousLocalization|GradedSMul".
  Hits include graded-module action infrastructure and ring localization; no general
  Proj module sheaf construction.
- `rg` in `WeilConjectures` found only `Proj.twist` in the relevant Proj files;
  `Twist.lean` explicitly lists constructing `M~` for arbitrary graded `M` as TODO.
  `grep -rn` for this item's id across `WeilConjectures` found no declaration.
- `rg` of `lean/Sheaf` and the DAG found `degreeZeroFractions`,
  `homogeneousPieceAway`, and the statement `gradedModuleAwayRestriction`.
  The first supplies exactly the equal-degree subset needed here and is reused.
  The latter theorem provides no module-sheaf construction. No existing theorem
  states all four clauses of this item.
- `tools/blueprint_refs.py search 'homogeneous localization'` found five ring-chart
  nodes, no alternate module-sheaf construction. The existing fraction node was
  located through its declaration record and its full module was read.
- `rg` of Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no declaration named `gradedModuleSheaf_exists` or
  `localizedModuleHomogeneousScalars`. The upstream-name bookkeeping was also inspected.

Validation: server `scompile.py` compiled the final module in 5.9 seconds with exit
code zero and no warnings. All lines are at most 100 characters. The delivery dry
run is the final check; the independent second reader supplies their own section.

## Second reading by K1

I read the node statement, its Stacks source place (Constructions, Section 01M3,
the text before Definition 01M6, Lemmas 01M4, 01M7 and 01MB), and the complete
declaration in `ProjGradedModuleSheafExists.lean`. The introduced objects and
their rendering are as follows.

- `S`, its `N`-grading `𝒜`, and `X = Proj 𝒜` are the explicit variables and
  `AlgebraicGeometry.Proj`; `D[f]`, `R[f]`, and `N[f]` are local notation for
  `Proj.basicOpen`, `HomogeneousLocalization.Away`, and
  `LocalizedModule.Away`.
- The graded module is `(M, 𝓜, h𝓜, hsmul)`, with the explicit internal direct-sum
  condition and the stated `S_n • M_z ⊆ M_(n+z)` hypothesis. No Noetherian,
  finite-generation, field, or characteristic hypothesis is added.
- Clause (a) is the existential `Z`, `rhoS`, and `rho` block. Its carrier is
  exactly `LocalizedModule.degreeZeroFractions`; it includes the open-inclusion
  relation, semilinearity, the representative formula, identities, composition,
  and bijectivity on equal opens.
- Clause (b) is the existential `F : ModX` and additive equivalences `alpha`.
  The three scalar/restriction equations and the quantified uniqueness of an
  isomorphism `phi` are all present, followed by `F.IsQuasicoherent`.
- Clause (c) is the existential `Zp` with the same degree-zero carrier over
  `T[x]`, followed by the additive stalk equivalences `mu`, their stalk scalar
  law, and the germ formula. `moduleStalkFunctor`, `stalkIso`, and `germ` are
  the recorded project notions.
- Clause (d) is the existential ring map `eta` and additive map `gamma`, with
  the chart restriction, compatibility, scalar law, and final universal
  existence-and-uniqueness implication exactly in the node's quantifier order.

The edge cases are covered: `Fidx` permits zero and nilpotent homogeneous
elements; empty Proj and zero rings/modules are allowed; `m = 0`, negative
graded module components, and degree-zero-only gradings are allowed; no
characteristic or degree-one-generation assumption appears. The universe is
explicitly shared by `S` and `M`, with all local binders explicit.

I repeated the existing-declaration searches with LeanFinder/Loogle/LeanSearch
and `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json`. They found only structure-sheaf and twisting
infrastructure, plus the already landed `degreeZeroFractions`; no declaration
states this Proj graded-module sheaf existence theorem. The dependency
`def-sc-degree-zero-module-fractions` was opened and its carrier was checked
against the node.

No mismatch was found between the node and the Lean signature. In particular,
the additive equivalences (rather than equality of carriers) correctly express
the chart identifications, while the explicit scalar equations preserve the
module content of the source. No file or node change was required. The module
compiles cleanly with `scompile.py`; only the theorem's permitted `sorry` remains.
