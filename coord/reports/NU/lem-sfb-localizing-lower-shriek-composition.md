## Worker report

The current DAG already contains the reviewed stage-2 statement for
`lem-sfb-localizing-lower-shriek-composition`, with declaration
`AlgebraicGeometry.ProEtale.CondensedRing.exists_localizingLowerShriekComposition` in
`Sheaf.Paper.LocalizingLowerShriekComposition`. I copied that exact module and node record into
this sandbox; no duplicate definition or alternate theorem is introduced. The theorem proof is
`sorry`, as required for stage 2.

The theorem binds a condensed coefficient sheaf `Λ` on the coherent profinite site with
`[MonObj Λ] [IsCommMonObj Λ]`; a prime `ℓ`, finite intermediate field `E`, and the disjunction
of ring-object isomorphisms to the finite-field coefficient objects. It binds a field `k` of
positive characteristic different from `ℓ`, schemes `X,Y,Z` over `Spec k` with separated,
locally-finite-type and quasi-compact structure maps, and separated locally-finite-type
quasi-compact morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` over the base. These are rendered by the
explicit `Fact`, `Scheme.Over`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and
`IsOver` binders in the theorem signature.

The first conclusion supplies preservation witnesses `hf`, `hg`, and `hgf` for every boundary
compactification of `f`, `g`, and `f ≫ g`, respectively, with source and target the exact
`localizingClosureProEtale` full subcategories and ambient object
`rightDerivedLowerShriekOfCompactification`. The second conclusion supplies, for every triple of
compactifications, a natural isomorphism between the composite `localizingLowerShriek` functors
and the functor for `f ≫ g`. The final universally quantified clause states the refinement
compatibility equation for arbitrary compactifications, dense refinements `rf`, `rg`, `rgf`, and
every object `K`; it uses the canonical
`compactificationRefinementComponent` maps and evaluates the middle refinement at the refined
`f` image. Thus it expresses independence of compactification through the recorded cocycle.

Dependency declarations used are the existing records for `sk-def-sfb-dc-setting`
(`AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and the bounded
constructible declarations), `sk-def-sfb-condensed-ring` (`Profinite.CondensedRing`),
`sk-def-sfb-qlbar-condensed` (`Profinite.padicAlgClRingObj`),
`sk-def-sfb-constructible` (`AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and its
bounded/Tor constructions), `sk-def-localizing-closure`
(`AlgebraicGeometry.ProEtale.localizingClosureProEtale`), `sk-prop-sf-existence`
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek`), and
`det-sf-comp-coherence-cocycle`
(`compactificationRefinementComponent` and `compactification_coherence_cocycle`). The
proof-only imports remain in the module exactly as recorded in the node proof route.

Edge cases checked include identity, proper, and open-immersion morphisms; empty schemes and
zero objects; nondense chosen compactifications; and the absence of any nonempty or nonzero
hypothesis. The signature keeps the single site universe and does not impose a boundedness or
finite-Tor condition on arbitrary objects of the localizing closure.

Searches for an existing declaration were made with `msearch.py` LeanFinder, Loogle, and
LeanSearch queries for compact-support/lower-shriek composition; `rg` over
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`; and Mathlib grep for
`lowerShriek`, `compactSupport`, and pushforward composition. Results were only ordinary
sheaf/module pushforward composition or unrelated compact-support APIs. The exact theorem was
already present in the project module cited above, so this delivery reuses it. No
`STATEMENT-DISPUTED` issue or node correction applies.

## Second reading by NU

I independently opened the current node statement and the copied theorem signature. Every
hypothesis is represented by an explicit Lean binder: coefficient structure and alternatives,
prime and characteristic assumptions, three schemes over the same base, and all morphism
properties. The three preservation witnesses are existential conclusions, and the natural
isomorphism has exactly the compactification-indexed functor endpoints. The final equation has
all three dense refinements, the canonical refinement components in the stated directions, the
middle component evaluated at the refined `f` object, and equality after the component of the
composition isomorphism. No hypothesis or conclusion is added, dropped, weakened, or
strengthened. The module compiled cleanly with `scompile.py`; only the expected theorem
`sorry` remains.
