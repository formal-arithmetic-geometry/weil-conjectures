# Q92 stage-2 delivery

## Worker report

The module `Sheaf.Algebra.Homology.BoundedInjectiveRHomModelSupport` states
`CategoryTheory.boundedInjective_rhom_model_support`, with its entire proof `sorry`.
Its three helper definitions have real data: `ringModuleComplex` applies the existing
constant-module embedding to complexes, `ringHomResolutionMap` applies the existing Hom
bifunctor to the fixed resolution unit, and `ringHomResolutionComparison` is the actual
`Localization.fac` isomorphism used by the recorded derived internal Hom definition.
No theorem is proved and no definition chooses an arbitrary isomorphism.

This repairs the H2 return on immutable head `b7c03a46cb3d`. The returned packet
was retained and its initial prescribed dry run passed mechanically (commit
`ece1f4b22b1`); the independent review identified the missing definition owner.
The theorem signature, helper data, source statement and accepted four proof steps
remain unchanged. The delivery wrapper rebases the packet against the live branch.

### Hypotheses and clauses

- A commutative ring: `(A : Type u) [CommRing A]`, with arbitrary explicitly bound universe u.
  No Noetherian, nonzero, coherent, finite-generation, or characteristic assumption occurs.
- Integer-indexed cochain complexes: `CochainComplex (ModuleCat.{u} A) ℤ` for I and every M.
  These are actual ordinary module complexes, not complexes with an extra chosen site action.
- The specified one-object site and D(A): `RingSiteModules A` is exactly the recorded
  bottom-topology site on `Discrete PUnit.{u+1}`, with constant ring `onePointRingSheaf A`.
  The existing `AlgebraicGeometry.ringComplexConstant` sends an ordinary module to that
  constant sheaf with identity restriction. `ringModuleComplex A` applies it termwise.
  Evaluation at the sole object is its inverse, since all site arrows are identities;
  both preserve kernels and cokernels sectionwise. Thus `DerivedCategory (RingSiteModules A)`
  is the node's stipulated one-object-site presentation of D(A), and Q of a module complex
  is written `DerivedCategory.Q.obj ((ringModuleComplex A).obj M)`.
  `[HasDerivedCategory.{w} (RingSiteModules A)]` selects the localization morphism universe;
  w is independent of u and no size equality is imposed.
- Termwise injectivity: `hI : ∀ q : ℤ, Injective (I.X q)`, in ordinary ModuleCat.
- Bounds: `(a b : ℤ) (hab : a ≤ b)` and
  `hIb : ∀ q : ℤ, q < a ∨ b < q → IsZero (I.X q)`.
- The module-valued total Hom is the exact recorded `CochainComplex.moduleHomComplex M I`.
  It retains the A-linear homogeneous cochains and signed differential. Its image under
  the same constant embedding is the target of the isomorphism θ M.
- The sheaf-to-module Hom comparison e is a family of complex isomorphisms. Its first
  equation says that, for every M, r, p, cochain section z and x in M.X p, the p-coordinate
  of `(e M).hom` applied to z at x is `ringHomEvaluate ... r p ... z x`. That is the actual
  recorded product projection evaluated on the identity object of the slice. Because the
  site has a single value and arrow, these coordinates determine the comparison uniquely,
  with its differential and A-action. This is Step 1 of the accepted proof, not an additional
  assumption about a chosen equivalence or a substitute definition of Hom.
- Canonical derived isomorphism: the existential family θ has type
  `RHom(QM,QI) ≅ Q Hom_A^bullet(M,I)` in the stipulated site presentation. RHom is exactly
  the recorded `derivedInternalHomOfUniverses.{u,u,u,w} ⊥ (onePointRingSheaf A)`.
  The second equation normalizes θ by
  `(θ M).hom ≫ Q.map (e M).inv ≫ Q.map (ringHomResolutionMap ...) =
    (ringHomResolutionComparison ...).hom`.
  The latter is the fixed localization factorization c. Since the target is K-injective,
  the localized resolution map u is invertible; the equation uniquely means
  θ = c followed by u inverse followed by Q(e). It rules out an arbitrary natural
  automorphism of a family of representing objects. No arbitrary resolution is a binder.
- For every chain map f:M'→M, the third equation is
  `θ_M.hom ≫ Q.map (embedding.map (moduleHomPrecomp I f)) = RHom.map (Qf.op, 𝟙 QI) ≫ θ_M'.hom`.
  Lean's diagrammatic composition writes the node's usual right-to-left composition in
  the opposite textual order. The declared map is the existing total-Hom precomposition,
  and no injectivity, quasi-isomorphism, or support assumption on f is imposed.
- Additional lower bound only for the support clause: for every M and integer n,
  `(∀ p : ℤ, p < n → IsZero (M.X p)) → ∀ r : ℤ, b-n < r → ...`.
  The two conclusions are `IsZero ((moduleHomComplex M I).X r)` and `IsZero` of the r-th
  `DerivedCategory.homologyFunctor` applied to RHom(QM,QI). They are termwise and derived
  cohomology vanishing, respectively. The comparison itself is in the derived category,
  not only a per-degree identification. The node requests no further per-degree iso.

### Recorded declarations reused

All original statement dependency statements and Lean records, together with the actual
source signatures and documentation, were read. The original interfaces are usable.

- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; the cohomology functor and
  its localization factorization are in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `def-sp-injective-resolutions`: `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `CategoryTheory.Injective`, precisely extension along monomorphisms. The item needs the
  injective-object clause, not a choice of a resolution of a module in degree zero.
- `def-sc-module-total-hom-complex`: `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex`, using `HomComplex.Cochain` and `HomComplex.δ_hom`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
  `CategoryTheory.derivedInternalHomOfUniverses` and its `_inverts` theorem. I read the
  definition's precise `Localization.lift` and fixed `kInjectiveResolutionFunctor` unit;
  the new comparison uses that same factorization and those same universes.
- `def-pc-ring-hom-extension-shared-definitions`:
  `Sheaf.Algebra.Homology.RingHomExtensionDefs`, `CategoryTheory.RingSiteModules` and
  `CategoryTheory.ringHomEvaluate`, with the shared `ringHomComplexProjection`.
- Direct statement dependency `def-pur-hom-complex`: `WeilConjectures.Algebra.Homology.HomComplex`,
  `CategoryTheory.homComplex` and `CategoryTheory.homComplexFunctor`.
- Proof input `lem-weil-pbc-bounded-below-injectives-kinjective`: its Mathlib match is
  `CochainComplex.isKInjective_of_injective`, in
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`, lines 133–135; the lower-bound
  instance and all injective terms are precisely its hypotheses.
- Proof input `lem-pur-rhom-well-defined`:
  `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`,
  `CategoryTheory.quasiIso_homComplex_map`; I read the whole signature/docstring, which
  requires both K-injective targets and both quasi-isomorphisms, as used in Step 2.

The existing constant-module embedding is cited through
`def-weil-pbc-ring-complex-godement-construction`, which supplies
`AlgebraicGeometry.ringComplexConstant` and its `_additive` instance from
`Sheaf.Paper.RingComplexGodementConstruction` (lines 65–85).
`def-pc-perfect-rhom-base-change-map` supplies the existing
`CategoryTheory.ringSiteModulesGrothendieck` from
`Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap` (lines 39–43).
Precomposition is now cited through the new definition node
`def-trf-module-hom-precomposition`, with `existing: true` on
`Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy` and declarations
`CochainComplex.moduleHomPrecompComponent`, `CochainComplex.moduleHomPrecomp_comm`
and `CochainComplex.moduleHomPrecomp`. The theorem dependency
`lem-trf-hom-dual-preserves-homotopies` has been removed: no homotopy result is needed.
The advisory was also applied: `def-pur-hom-complex` is a direct statement dependency
and its upstream module is explicitly publicly imported.

### Sources, searches and edge cases

Read local `dualizing.tex` lines 2574–2602 (Tag 0G4H, including truncation and its upper
vanishing), `sites-cohomology.tex` starting at line 8836 (Tag 08J7, the K-injective
construction and bifunctor), and the recorded Hom-complex and invariance declarations.
The accepted node's proof is included step by step in the theorem docstring.

Actual searches, through the prescribed `msearch.py Q92 <item>` wrapper, are in the
sandbox `searches.jsonl`:

- LeanFinder: “Derived internal Hom into a bounded injective complex is canonically the
  module total Hom complex naturally in its source and vanishes above the target upper
  bound minus the source lower bound” returned eight hits, including
  `CochainComplex.isKInjective_of_injective`, `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`,
  and `HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKInjective`.
  They supply K-injectivity or external Hom groups, not this module-valued canonical
  comparison with naturality and both support conclusions.
- Loogle: `CochainComplex.moduleHomComplex, CategoryTheory.derivedInternalHomOfUniverses`
  returned zero hits with the diagnostic “unknown identifier 'CochainComplex.moduleHomComplex'”.
  These are project names, so this search does not establish their absence from the project.
  The exact project declarations were found and reused by source search.
- Mathlib grep: `moduleHomComplex|derivedInternalHom|RingSiteModules`, subdirectory
  `Algebra/Homology`, returned zero hits. These names belong to the project.
- LeanSearch: “Derived internal Hom into a bounded injective complex is naturally
  represented by the module total Hom complex and vanishes above the difference of
  support bounds” returned eight hits, including the injective single-target vanishing,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, and localized shifted-Hom facts.
  None states the requested internal-Hom model and coordinate-normalized naturality.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `moduleHomComplex`, `RingSiteModules`,
  `onePoint`, `ringComplexConstant` and `moduleHomPrecomp` found the reused declarations
  listed above. The node id was searched in upstream Lean and `dag/lean_names_upstream.json`;
  no existing declaration states this item's complete conclusion. DAG searches found the
  existing owners for the constant-module embedding and precomposition; no copies were made.

The zero ring, zero I, zero M and an interval a=b are all allowed. The integers a,b,n may
be negative, M may be unbounded in both directions for the comparison, and it has only
its stated lower support bound for vanishing. At r=b-n there need not be vanishing:
modules concentrated in degrees n and b over a field give a nonzero Hom there, validating
strict `<` in the upper-bound hypothesis. For r>b-n, every factor of the infinite product
is zero by the source-zero/target-zero dichotomy; no finiteness of that product is assumed.
The ring and module universe u is arbitrary, the localization universe w is arbitrary,
and the site has object and arrow universes u as required by the existing presentation.
No disputed statement or source error was found.

### Validation

The first prescribed compile identified missing instance visibility for the existing
constant functor and Grothendieck category. I explicitly use the existing additive
instance inside `ringModuleComplex`, import the existing Grothendieck instance owner,
and allow definitional reduction of the existing constant embedding. No data or
hypothesis was added. The final `scompile.py` run compiled both its sandbox validation
and the actual library module cleanly, in 20.3 and 20.5 seconds respectively, under the
unchanged 60-second limit. There are no diagnostic commands, extra axioms, or auto-bound
variables. Dry-run and delivery results are recorded by the prescribed delivery wrapper.

## Second reading by Q92

This is the dispatcher's requested worker self-check, not a claim that another agent was
started: the brief expressly forbids starting agents, and the maintainer supplies independent
review. I reopened the node statement, all four accepted proof steps, and the complete final
Lean module. The returned stage-2 payload was retained. The second reading checked
that all three helpers are actual constructions from recorded declarations and that the
single theorem's only proof is `sorry`.

In particular, the ring, injectivity, interval and bound hypotheses match the first sentence;
M is quantified without restrictions in e and θ; the target is the recorded A-module-valued
Hom complex embedded in the specified site; and the first two equations uniquely normalize
e and θ using the actual product projections and fixed resolution unit. The naturality
square has the correct direction for f:M'→M in Lean's diagrammatic composition and uses
ordinary precomposition. The final clause places the lower-bound hypothesis only on its
vanishing assertion, asserts both zero terms and zero derived cohomology, and uses strict
r>b-n. The field-concentrated example confirms the endpoint is not accidentally included.
The D(A) presentation is exactly the stipulated one-object site, through the already existing
constant embedding; it introduces no independently chosen equivalence, resolution or map.
No statement correction is necessary. The item node deltas are its Lean record and statement dependencies. The new definition
node owns exactly the existing precomposition construction, without assuming any conclusion
of the homotopy-preservation theorem. The additional direct Hom-complex dependency records
the construction used by the comparison and resolution map. No mathematical statement
correction is necessary.


## New nodes

`def-trf-module-hom-precomposition` is the definition of first-variable precomposition
on module-valued total Hom complexes, sourced to Stacks Tag 0A8H,
`more-algebra.tex`, `section-hom-complexes` (lines 17850–17870).
For arbitrary commutative A and complexes P,R,T, with f:P→R, its degree-j map is the
existing `moduleHomPrecompComponent T f j`, sending φ to φf and retaining A-linearity.
The existing proved `moduleHomPrecomp_comm` is the compatibility with D, and the
existing `moduleHomPrecomp T f` packages those components as a chain map. These are
all three declarations requested in the return. There is no new Lean module or duplicate
definition; the new node has `existing: true` on the unchanged landed module.
The context's A, P and R are explicitly bound by that module's universe/variable commands.
The node's Lean signature is copied verbatim from `noncomputable def` to `where`.

The three new searches are recorded verbatim in the node from `searches.jsonl`:
LeanSearch for “Precomposition by a cochain map defines a chain map on module valued
total Hom complexes” returned eight hits (cochainsMap, single-target precomposition,
mapBifunctorMap and homogeneous-cochain composition); Loogle for
`CochainComplex.HomComplex.Cochain.ofHom, CochainComplex.HomComplex.Cochain.comp`
returned twelve hits, including `δ_ofHom_comp`; Mathlib grep for
`moduleHomPrecomp|δ_ofHom_comp` in `Algebra/Homology` found the latter at line 762.
`rg -l 'moduleHomPrecomp|total Hom.*precomposition|precomposition.*total Hom'` over
`dag/nodes`, `lean/WeilConjectures` and `lean/Sheaf` found the existing theorem node and
its implementation, but no definition node owning precomposition. The exact-name source
search also found callers in FrameDualMate. `tools/blueprint_refs.py search
'precomposition'` found ten blueprint nodes about other notions; none defines this
module-valued chain map. `ancestor` returned `lem-trf-local-term-locality`, as recorded.
The new definition uses only the two existing definition dependencies for complexes
and total Hom, so it cannot depend back on this item. Zero f, zero source or target,
the zero ring, arbitrary unbounded complexes and negative j are all allowed. The chain
map condition follows componentwise from f commuting with differentials and uses no
boundedness, injectivity or homotopy hypothesis.

### Repair self-check

H2 is repaired by replacing the theorem owner in the item's `stmt_deps` with
`def-trf-module-hom-precomposition`, whose declaration list is exactly the three requested
names. The existing module is not edited. The item still imports it for the same chain map.
The advisory is addressed by adding `def-pur-hom-complex` and its explicit public import.
I reread the new node against the actual definitions and the source: the component formula,
A-linearity and differential compatibility agree. The new node introduces no homotopy
claims, and the reviewed canonical comparison, naturality equation and support conclusion
are unchanged. No other node is edited, and no proof is added.


### Repaired packet validation

The prescribed `scompile.py Q92 lem-trf-bounded-injective-rhom-model-support
lean/Sheaf/Algebra/Homology/BoundedInjectiveRHomModelSupport.lean` completed with exit
code zero after both the sandbox and actual library-module checks, with no diagnostics.
The item signature was compared verbatim with `lean.statement`; it matches and the module
contains exactly its one theorem `sorry`. Comparing the item node against the current
read clone found only `lean` and `stmt_deps` changes. The new definition node has exactly
the fields required by §5 and an existing declaration record, so it adds no Lean file.
The repaired `deliver2.py --no-push` passed preflight and all compilation checks at
`b43ed9031c4`, staging exactly the report, the two node files and the item's module.
This is a substantive repair of returned head `b7c03a46cb3d`, not an unchanged re-push.
