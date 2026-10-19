## Worker report

The delivery states all three clauses of `det-sf-mate-open-restriction`, without a statement
change, in `Sheaf.Paper.MateOpenRestriction`. The four theorem proofs are `sorry`:
`mateOpenImmersion`, `mateOpenSourceRestriction`, `mateOpenTargetRestriction`, and
`mateOpenCover_isIso`, in namespace `AlgebraicGeometry.ProEtale.CondensedRing`.
All eight helper definitions have real data. There are no new independent notions or nodes.
The resolved stage-1 repair note was read: its request concerned splitting the proof and
keeping the statement unchanged. This delivery retains the current statement and proof.

Hypotheses, one by one:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]` in every theorem.
- The field and positive characteristic different from ℓ are `(k : Type u) [Field k]`,
  `(p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)`.
- The separated finite-type standing schemes have `[X.Over (Spec (.of k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, `[QuasiCompact ...]`, `[IsSeparated ...]`,
  and the same binders for Y where Y occurs. Finite type means locally finite type plus
  quasi-compactness. These hypotheses imply qcqs, and Noetherianity. Open schemes U and V
  carry their induced structures over k, through j, a or v; no independent structure map
  on an open scheme is chosen. Hence every open in the statement is included, including
  opens without an already installed `Over` instance.
- The standing separated finite-type k-morphism is `(f : X ⟶ Y)` with
  `[f.IsOver (Spec (.of k))] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`.
- Λ is a condensed abelian sheaf with `[MonObj Λ] [IsCommMonObj Λ]`, as in the recorded
  internal-module framework. `_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ` is precisely
  the recorded six-case admissibility predicate: finite discrete ℓ-power-torsion rings,
  Zℓ, Qℓ, finite subextensions E, their integer rings, and the topological algebraic
  closure. It records the finite subextension/valuation-ring choices existentially rather
  than imposing an unrelated field on cases where none is needed.
- Every category used is `(localizingClosureProEtale Λ T).FullSubcategory` of the ordinary
  unbounded derived category of internal modules over `condensedRingObj Λ T = Λ_T`.
  This uses the recorded constant-model Dctf, fixed-size coproduct closure and no completion.
- Exceptional inverse images in clauses (2) are `(G, adjF)` for the actual
  `localizingLowerShriek Λ c hf`. The witness hf certifies only membership of images;
  the functor's objects and maps are the existing `Rp_* D(i_!)`. These are universally
  quantified Brown-adjunction choices, not an ambient exceptional functor or additional
  geometric assumption. The dependency supplies these choices. Compactification
  independence allows any c; finite type of f makes its open part quasi-compact.

Clauses, one by one:

1. `mateOpenImmersion` takes `j : U ⟶ X`, `[IsOpenImmersion j] [QuasiCompact j]`.
   Its existential he and hs give the restrictions of actual `D(j_!)` and `D(j^*)`.
   `adj : mateOpenExtension Λ j he ⊣ mateOpenPullback Λ j hs` is the claimed adjunction.
   The first equation specifies that its Hom bijection is the ambient termwise open
   adjunction, rather than a separately chosen adjunction. The ht witness restricts
   `Rf_!` for `Compactification.ofIsOpenImmersion j = (j,id)`. For every Brown right
   adjoint G of that functor the theorem gives `∃! e : G ≅ mateOpenPullback Λ j hs`.
   Its equation is compatibility of the two counits, using the explicitly constructed
   `mateOpenTrivialLowerShriek` to identify `R(id)_* D(j_!)` with `D(j_!)`.
   Together with the triangles this gives compatibility with units and all Hom bijections.
   The recorded Brown independence comparison transports this identification to any
   compactification used to name j!.
2. `mateOpenTargetRestriction` takes an arbitrary open Cartesian square
   `sq : IsPullback a q f v`, where a and v are open immersions. Thus U is X_V, a is u,
   q is f_V and v is the target inclusion, up to the unique isomorphism of pullbacks.
   `c.ofIsPullback sq` is the actual upstream base-changed compactification.
   he, hs, hv and hq establish all required restrictions. The theorem also asserts
   existence of a right adjoint for q. For every such Brown choice J, it gives
   `∃! e : G ⋙ mateOpenPullback Λ a hs ≅ mateOpenPullback Λ v hv ⋙ J`, which in
   ordinary composition order is `u* f! ≅ f_V! v*`.
   Canonicity is not expressed by bare nonemptiness: for every M, N and test map b,
   the final equation says its transpose is restriction of the transpose of b under
   the original Brown and open adjunctions. The left multiplier
   `mateOpenTargetLowerShriek Λ sq c M.obj` is a fully constructed map
   `v* Rf! u! M → Rf_V! M`. It uses the pullback compositor, proper direct-image
   counit, the two canonical open-extension compositors, and the inverse open unit.
   There is no arbitrary square comparison or arbitrary natural map in the hypotheses.
   `mateOpenSourceRestriction` gives the second comparison. For every source open j it
   produces the adjunction for `Rf_j!` in `c.precomp j` with right adjoint `G ⋙ j*`.
   Its Hom equation uses the explicit canonical `mateOpenSourceLowerShriek`.
   The final universal clause gives the unique counit-compatible isomorphism from that
   restriction to every Brown right adjoint J of `Rf_j!`, namely `j* f! ≅ (fj)!`.
3. `mateOpenCover_isIso` takes any `I : Type w`, `U : I → X.Opens`, and
   `_hcover : iSup U = ⊤`. For any morphism b in the full localizing category,
   `_hb : ∀ i, IsIso ((upperStar Λ (U i).ι).mapDerivedCategory.map b.hom)` implies
   `IsIso b`. Ambient restrictions are used here because a fully faithful inclusion
   reflects isomorphisms; this is the same assertion about the restricted functors.
   The universally quantified source-open and target-open comparison theorems apply
   to each member of either cover, giving both final displayed locality formulas.
   No cohomological bound is imposed on objects or morphisms.

The helpers are constructions of these exact comparisons, not replacement functors:
`mateOpenPullback` and `mateOpenExtension` are `ObjectProperty.lift` of the existing
termwise functors; `mateOpenExtensionComp` is left-adjoint uniqueness applied to the
existing coefficient-compatible `upperStarComp`; `mateOpenSourceLowerShriek` is its
whiskering by the unchanged proper pushforward; `mateOpenProperRestriction` is the
specified ordinary direct-image counit mate; `mateOpenSquareExtension` transports the
actual commuting open square; `mateOpenTargetLowerShriek` applies that transport,
the direct-image mate and inverse open unit; `mateOpenTrivialLowerShriek` uses the
existing canonical derived direct-image identity.

Dependency declarations used (with their recorded modules):

- `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its standing
  `Over`, separated and finite-type scheme convention. This statement accepts every
  compactification, including the recorded Nagata choice; no second choice is constructed.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient` and
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` (the closure exported through
  that module). This is the live independently sized closure, not a redefinition.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and
  `ConstantModelConstructibleFiniteTor`, used by the recorded closure.
- `det-sf-existence-brown`: `Sheaf.Paper.BrownExceptionalAdjoint`,
  `AlgebraicGeometry.ProEtale.CondensedRing.exists_brownExceptionalAdjoints`, including
  its unique compatible comparisons between all compactifications; the underlying
  `localizingLowerShriek` comes from its imported `Sheaf.Paper.LocalizingExceptionalAdjoint`.
- `sk-def-sfb-module-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`,
  `CondensedRing.openImmersionLowerShriek` and
  `openImmersionLowerShriekUpperStarAdjunction` (fully qualified with the namespace above).
- `sk-def-sfb-module-derived-lower-shriek`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `CondensedRing.rightDerivedLowerShriekOfCompactification`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-pbc-scheme-conventions` is the recorded convention node, with no declaration:
  use Mathlib's `Scheme`, `QuasiCompact`, `LocallyOfFiniteType`, `IsSeparated`, `IsPullback`.

The exact termwise open adjunction is
`CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction` from the published
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`.
Its signature and docstring, the underived definitions, both derived lower-shriek definitions,
the constructibility definitions, coefficient predicate, Brown theorem, and upstream
compactification `precomp` / `ofIsPullback` were read. Proof-dependency modules with existing
statements are imported, including exact derived factorization/adjunction, both coefficient
composition statements, the Brown hypotheses (through BrownExceptionalAdjoint), cartesian
coefficients, weakly-etale localization and the recorded Mathlib leaves. This introduces
no import cycle. No dependency record needs repair.

Edge cases checked before writing and in the final reading:

- Empty U, V and X_V: extension is zero, inverse images and the base-changed
  compactification are still defined; none of the binders requires nonemptiness.
- Empty cover: `iSup U = ⊤` forces X empty, and all its module-derived objects are zero;
  no `Nonempty I` restriction is introduced. Infinite and arbitrarily indexed covers
  are included, since w is independent of u. Their image is a set of opens of X.
- Identity opens and identity covers: both unit-normalized compositors and the counit
  mate reduce to the same adjunction identifications; no distinct-open condition appears.
- The zero morphism, zero objects and zero coefficient ring are allowed. Finite rings
  killed by ℓ^0 are included by the dependency's admissibility predicate.
- The schemes need not be smooth or proper, and the objects need not be bounded or
  themselves constructible. Only membership in the recorded uncompleted localizing
  closure is required.
- The target square allows any pullback representative, not just a chosen literal
  inverse-image open; isomorphic representatives therefore remain covered.
- Site/coefficient universes stay the recorded u, u+1 levels. No independent test universe
  or size equality restricts the mathematical statement.

Searches for existing declarations:

- `msearch.py leanfinder`, query "For an open immersion extension by zero is left adjoint
  to restriction and exceptional inverse image restricts locally on source and target":
  8 results, chiefly Mathlib's Zariski `Scheme.Modules.restrictAdjunction` and
  `restrictFunctorIsoPullback`. These concern structure-sheaf modules on the Zariski site,
  not these condensed pro-etale localizing categories or Brown exceptional functors.
- `msearch.py loogle`, query `Adjunction.rightAdjointUniq, IsOpenImmersion, upperShriek`:
  no hits (the unqualified Adjunction identifier is not recognized). A second query,
  `CategoryTheory.Adjunction.rightAdjointUniq`, returned the actual uniqueness API,
  used through `Adjunction.leftAdjointUniq` for canonical open composition. This is
  abstract uniqueness, not this geometric statement.
- `msearch.py grep`, query `upperShriek|openImmersionLowerShriekUpperStarAdjunction`
  in Mathlib CategoryTheory: no hits. Query
  `upperShriek.*open|open.*upperShriek|exceptional.*restriction` in AlgebraicGeometry:
  no hits.
- `rg` of the upstream WeilConjectures and project Sheaf trees for the node id and
  `upperShriek.*[Oo]pen|[Oo]pen.*upperShriek`: only downstream references in
  `RestrictionLocal.lean` and `AffineSpaceRationalLine.lean`, not the statement.
  The upstream upper-shriek/six-operations interfaces concern bounded-constructible
  categories and additional operation data, so they do not replace these Brown adjoints.
- Exact-name `rg` over Mathlib, WeilConjectures and lean/Sheaf for all new declaration
  names: no existing declarations. Existing open adjunction, inverse-image compositor,
  compactification precomposition and base change were reused rather than copied.

Validation: `scompile.py NA det-sf-mate-open-restriction <module>` compiled both the sandbox
module and its library path without errors or warnings. The delivery dry run supplies
an additional per-file compile and server preflight. No statement dispute or node fault.

## Second reading by NA

A separate final reading reopened the DAG statement, the blueprint source and the finished
module, and matched each clause as listed above. The reading checked in particular that
j! is levelwise open extension, f! is a right adjoint of the actual compactification
composite on Loc(Dctf), and both comparison equations determine natural isomorphisms
rather than unconstrained maps. It also checked the order of functor composition:
`G ⋙ a*` is u* f!, and `v* ⋙ J` is f_V! v*. Source comparison uses `c.precomp j`,
and target comparison uses `c.ofIsPullback sq`, so their proper/open maps are canonical.

The initial clause-(1) form compared right adjoints of open extension directly. This was
made explicit for the Brown functor itself: the final statement has ht for the trivial
compactification and uses `mateOpenTrivialLowerShriek` in the counit equation. The source
and target comparisons already carried their actual Hom normalizations. A dependent
transport equality for open extensions was changed to congruence with proof irrelevance
so that its data compile; this did not change any signature or mathematical condition.
The cover clauses follow by instantiating the universal comparison theorems at each open.
No missing hypothesis, coefficient case, empty case, weaker conclusion or arbitrary
comparison remains. No node statement or dependency record was changed. In accordance
with the dispatcher brief, no additional agent was started; the maintainer's independent
review remains the independent review of this delivery.
