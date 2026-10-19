## Worker report

The module `Sheaf.AlgebraicGeometry.TowerCompositionRefinement` states
`AlgebraicGeometry.Etale.cbcTowerComposition_refinement` with its proof `sorry`.
Four real definitions spell out the component arrows, without postponed construction
data: `cbcTowerRefinementComponent`, `cbcTowerOpenCompositionComponent`,
`cbcTowerCompositionComponent`, and `cbcTowerCompositeRefinementComponent`.
All five declarations belong to this node and are recorded in `lean.declarations`.
No node statement or dependency record changes.

Hypotheses and clauses, matched to the Lean:

- Finite commutative coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  All objects are `DerivedCategory.Plus (Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} Λ))`, the ordinary small-etale constant-coefficient category.
- Schemes and composable arrows: `{X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)`.
  Each morphism is separated and finite type via `IsSeparated`, `LocallyOfFiniteType`
  and `QuasiCompact`. These are morphism properties, not absolute qcqs hypotheses.
- Each supplied compatible tower is a `Compactification.Triangle f h` from the
  dependency's recorded module. Its `cg.i,cg.g` are i,q; `cfg.i,p` are a,p;
  `cf.Z,q,cf.g,cf.i` are U,b,pY,c. The three compactification fields supply proper
  second maps and open first maps, and `isProper_p` supplies proper p. The explicit
  `QuasiCompact` instances on cf.i,cg.i,cfg.i,q supply the stated qc open maps.
- The triangle's `cg.comm` gives i q = h; `cfg_i_p` gives a p = f i.
  Its `i_q` gives c b = a and `cf.comm` gives c pY = f. Its `isPullback` identifies
  U with the stated fibre product by the unique projection-preserving isomorphism.
  Thus using the already recorded triangle does not select a special tower.
- Proper u,v,w are the explicitly bound `uY,v,w` with their `IsProper` instances.
  The seven equations are respectively `hi,ha,hc,hb,hp,hs,hq`. In Lean diagrammatic
  order these read i1 u = i2, a1 v = a2, c1 w = c2, b1 v = w b2,
  v p2 = p1 u, w pY2 = pY1, u q2 = q1. In particular no `IsPullback` is assumed
  for (b1,b2,w,v); `Compactification.Triangle.Hom` is deliberately not used because
  it carries additional cartesian refinement conditions.
- F is c! followed by RpY,*; H is i! followed by Rq,*; E is a! followed by
  R(cfg.g), with `p_g` identifying cfg.g = p q. These are the actual dependency
  functors `openImmersionLowerShriek.mapDerivedCategoryPlus` and
  `rightDerivedLowerStarPlus`, not arbitrary functors of abstract categories.
- `cbcTowerCompositionComponent` is precisely Rq applied to gamma at c!K,
  then Rq Rp applied to the degreewise exact open compositor (and the equality
  c b = a), then the direct-image compositor Rp Rq -> R(p q).
  `cbcOrdinaryGamma` is the direct ordinary derived projection of the `γ` witness
  in `Etale.properOpenInterchangeCoherence`: its body is
  `(properOpenInterchangeCoherence Λ).choose_spec.choose` applied to the square. Its
  source and target are ordinary small-etale D+ functors over finite commutative Λ, and
  the witness carries the theorem's unit, refinement, horizontal, vertical, identity,
  and base-change normalization clauses. No strict-tower or pro-etale data is involved.
- `cbcTowerRefinementComponent Λ C1 C2 w hi hg K` is Rp2 applied to the exact
  recorded `properOpenComparison` alpha_w, followed by the direct-image compositor
  for pY1 = w pY2. It supplies C_f with cf, and C_h with cg.
- `cbcTowerCompositeRefinementComponent` supplies C_hf with cfg. Its equality
  cfg1.g = v cfg2.g is derived inside the definition from hp,hq and both p_g
  equations; this proof is a concrete equality transport, with no extra hypothesis
  and no postponed theorem.
- The conclusion in diagrammatic order is `mu2 ≫ C_hf = H2.map C_f ≫ C_h ≫ mu1`,
  at every `(K : D+(X_et,Λ))`. This is exactly the displayed natural-transformation
  equation by `NatTrans.ext`, without an additional naturality assumption or a
  restriction on K. The component form avoids duplicating naturality theorems
  for the already defined canonical alpha maps.
- The canonical direct-image composition is `Functor.rightDerivedFunctorPlusCompIso'`
  applied to `lowerStarComp`, in the iterated-to-composite orientation. Its inverse
  is the normalized d in `lem-cbc-etale-derived-direct-image-coherence`; the latter's
  source explicitly names the upstream associativity theorem for this same canonical
  compositor. Exact extension composition uses `extensionZeroCompDerivedPlusIso`,
  which localizes `openImmersionLowerShriekComp` degreewise.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficient module:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, with Mathlib `DerivedCategory.Plus`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  `...Derived.UpperLowerStarCoherence`: `Etale.rightDerivedLowerStarPlus`;
  `...UpperLowerStar.Coherence`: `Etale.lowerStarComp`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`,
  `Etale.preservesFiniteLimits_openImmersionLowerShriek` (exact extension).
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`:
  `exists_compactifiable_compatible_tower` and its public upstream
  `Compactification.Triangle` interface; the supplied data, not its existence proof,
  enter the statement.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `Etale.properOpenInterchangeCoherence`, including its normalization, refinement,
  horizontal and vertical clauses.
- `Sheaf.AlgebraicGeometry.ProperOpenComparison`: `Etale.properOpenComparison`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `Etale.properOpenInterchangeCoherence`; the local `cbcOrdinaryGamma` projects its
  ordinary derived `γ` witness directly, with no strict/pro-etale category involved.
- `Sheaf.Paper.EtaleDerivedDirectImageCoherence`:
  `Etale.exists_normalizedDerivedDirectImageCoherence`, the proof-plan coherence input.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `Etale.openImmersionLowerShriekComp_coherence` and the existing
  `Etale.openImmersionLowerShriekComp`.
- The interchange dependency imports
  `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`, whose real
  `Etale.extensionZeroCompDerivedPlusIso` is used unchanged.

Edge cases checked before writing: the zero coefficient ring is permitted (no
`Nontrivial Λ`); the empty scheme and the zero derived object are permitted;
identity refinements and identity f,h remain admitted; towers with extra proper
components remain admitted, since no cartesian refinement is imposed. Independent
ambient scheme universes are not restricted beyond the source convention of schemes
in one universe, and coefficients occupy the documented u+1 lift. No characteristic,
Noetherian, absolute quasi-compactness or quasi-separatedness assumption is introduced.
There are no index-set or degree restrictions. No statement dispute was found.

Searches for an existing exact declaration:

- msearch leanfinder, "Composition of compact support direct images in compatible
  compactification towers commutes with proper refinement maps": 8 unrelated hits,
  including `CompactlySupportedContinuousMap.comp_assoc`, `TopologicalSpace.Compacts.map_comp`,
  and `OnePoint.map_comp`; no derived-etale statement.
- msearch loogle, `AlgebraicGeometry.IsProper, CategoryTheory.NatTrans`: 0 hits.
- msearch grep, `properOpen|[Tt]ower.*[Rr]efinement`: 0 Mathlib hits.
- msearch leansearch, "proper open interchange compactification tower refinement derived
  etale direct image composition": 8 hits, including proper morphism composition,
  scheme module restriction composition, and ring etale composition; no exact match.
- rg over upstream WeilConjectures and project lean/Sheaf for tower/refinement,
  tower composition and the node id: upstream has no exact declaration. Side hits
  `StrictTowerCompositionPasting` and `CompleteCompactSupportProetale` concern
  pro-etale strict towers/completed coefficients; `UnboundedCompactSupportProperComposition`
  concerns unbounded categories. Their signatures were read and do not match ordinary
  small-etale D+ at finite coefficients. The new declaration names and node id have
  no upstream/name-index match.

Sources read: the full item and all nine statement-dependency statements/records;
recorded source signatures and docstrings; Stacks more-etale.tex labels
lemma-shriek-proper-and-open-compose and -compose-horizontal (Tags 0F7C/0F7D);
the current main-20261015 blueprint's thm-cbc-finite-torsion statement. Missing local
recorded source `WeilConjectures.AlgebraicGeometry.DerivedCategories` was read with
`scompile.py --source`, as was the live interchange module.

The exact-name search for `properOpenInterchangeCoherence` found its full ordinary
derived coherence interface. The module defines `cbcOrdinaryGamma` by projecting the
second witness of `Etale.properOpenInterchangeCoherence`; its complete signature is an
ordinary small-etale D+ natural isomorphism with the same unit, refinement, horizontal,
vertical, identity, and base-change normalization clauses. This direct projection avoids
the previous `ProEtale.StrictTower.finiteGamma` route and adds no mathematical dependency
beyond the cited ordinary interchange theorem.

Validation uses only the prescribed scompile.py and deliver2.py wrappers. Equality
transport of the named open composite is a real equality-elimination construction.
No file timeout or heartbeat limit is raised; temporary reduced-heartbeat diagnostic
settings are absent from the delivered module.

The final standalone scompile check passed with no errors or warnings: sandbox 3.5 s,
library 4.2 s. The prescribed deliver2.py --no-push check also printed OK: its
candidate commit c27aa6621a passed the maintainer preflight and per-file compilation.

## Second reading

The repaired module uses `cbcOrdinaryGamma`, whose source and target are explicitly
`rightDerivedLowerStarPlus` and `openImmersionLowerShriek.mapDerivedCategoryPlus` on
ordinary small-etale sheaves of `ModuleCat Λ`. It is obtained from the `γ` witness of
`Etale.properOpenInterchangeCoherence`; the witness is selected together with the
corresponding ordinary `δ`, so its normalization clauses are the theorem's clauses rather
than an arbitrary isomorphism. The composition component applies this ordinary comparison
at `T.q`, `T.cf.g`, `T.p`, and `T.cg.i`, then the exact open-extension compositor and
the ordinary derived direct-image compositor. No pro-etale tower, strict-tower object,
completed coefficient, or extra hypothesis enters the statement.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
