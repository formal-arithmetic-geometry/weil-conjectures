## Worker report

The delivery binds `lem-sfb-eta-comp` to the existing theorem
`AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. No Lean module is delivered:
the exact statement already exists. The authoritative published source was read with
`scompile.py --source`; in that source the theorem is at lines 654–664. The older
slopmaster2 checkout does not contain this module. The `slopmaster2` branch label is
used consistently with the dependency records for this published WeilConjectures root.
Only the item's `lean` field is changed.

Clause-by-clause correspondence:

- A condensed ring is a ring object on `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}`, encoded by `MonObj Λ`. The existing equality is on underlying abelian
  sheaves; its `omit [MonObj Λ]` removes the unused ring structure from its type.
  Thus the declaration applies to every condensed ring, including noncommutative
  and zero rings, without needing any additional property.
- Arbitrary schemes and arbitrary composable morphisms are the section parameters
  `{X Y : Scheme.{u}} (f : X ⟶ Y)` and theorem parameters
  `{Z : Scheme.{u}} (g : Y ⟶ Z)`. There is no finite, weakly étale, proper or
  nonempty hypothesis on either morphism or any scheme.
- The structure map `π_T` is `toSpecZ T`, with `comp_toSpecZ h` giving
  `h ≫ toSpecZ B = toSpecZ A`.
- The node's `p^*` is `pointUpperStar`, and its `F = p^* Λ` is
  `pointUpperStar.obj Λ`. `upperStarFromPoint T` is definitionally
  `pointUpperStar ⋙ (toSpecZ T)^*[Ab.{u + 1}]`.
- `Λ_T` is `condensedRingObj Λ T`, definitionally
  `(upperStarFromPoint T).obj Λ`. The bundled coefficient ring is
  `coefficientRing T (Mon.mk Λ)`; its underlying object is the same sheaf.
- For arbitrary `a : A ⟶ B`, `b : B ⟶ C`, the node's `c_{a,b}` is
  `lowerStarComp Ab.{u + 1} a b`. Its construction is the sheaf pushforward
  comparison induced by the inverse pullback-pasting isomorphism, as in the
  dependency's recorded declaration.
- The explicit normalization is already the construction in the published source.
  Set `adj₁ = upperStarLowerStarAdjunction Ab (a ≫ b)` and
  `adj₂ = (upperStarLowerStarAdjunction Ab b).comp
  (upperStarLowerStarAdjunction Ab a)`. Then
  `upperStarComp Ab a b = ((conjugateIsoEquiv adj₁ adj₂).symm
  (lowerStarComp Ab a b).symm).symm`.
  Therefore `(upperStarComp Ab a b).symm` is precisely the node's `m_{a,b}`,
  not an arbitrary comparison. `coefficient_conjugateEquiv_upperStarComp_inv`
  records that its conjugate is `(lowerStarComp Ab a b).inv`.
  `unit_conjugateEquiv_symm adj₁ adj₂` gives exactly the stated unit equation;
  injectivity of the adjunction Hom equivalence gives uniqueness. There is no
  extra compatibility hypothesis.
- `upperStarFromPointComp h` whiskers this inverse pullback comparison by
  `pointUpperStar` and follows it by the equality-induced identification from
  `comp_toSpecZ h`. Its component is `condensedPullbackHom Λ h`, the recorded
  `α_h`; `condensedPullbackHom_eq` also exposes that formula explicitly.
- `condensedPushforwardHom Λ h` is the recorded `η_h`: the unit of
  `upperStarLowerStarAdjunction Ab h`, followed by `(lowerStar Ab h).map`
  of `condensedPullbackHom Λ h`. The `unitAlgHom` in its definition is the
  adjunction unit on the underlying sheaf, not an independent map.
- The conclusion is exactly
  `condensedPushforwardHom Λ (f ≫ g) = condensedPushforwardHom Λ g ≫
  (g)_*[Ab.{u + 1}].map (condensedPushforwardHom Λ f) ≫
  (lowerStarComp Ab.{u + 1} f g).hom.app (condensedRingObj Λ X)`.
  Lean's `≫` writes composition in execution order, so this is precisely
  `η_{g ∘ f} = c_{f,g}(Λ_X) ∘ g_*(η_f) ∘ η_g`, with source `Λ_Z` and
  target `(g ∘ f)_* Λ_X`.

Dependency declarations read and used:

- `def-sfb-eta`: `AlgebraicGeometry.ProEtale.condensedPushforwardHom`,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `def-sfb-alpha`: `AlgebraicGeometry.ProEtale.condensedPullbackHom`, same module.
- `def-sfb-pullback-from-point-comp-iso`:
  `AlgebraicGeometry.ProEtale.upperStarFromPointComp`, same module.
- `def-sfb-upper-star-from-point`:
  `AlgebraicGeometry.ProEtale.upperStarFromPoint`, same module.
- `sk-def-sfb-pulled-back-coefficients`:
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`, same module.
- `def-sfb-finite-lower-star-comp`:
  `AlgebraicGeometry.ProEtale.lowerStarComp`, recorded under
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
  The current published source is a compatibility re-export of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`;
  that canonical module's full declaration and docstring were read.
- `def-sfb-finite-upper-lower-star-adjunction`:
  `AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`, the same re-export
  and canonical module. This is the ordinary adjunction on abelian sheaves.
- `def-weil-pbc-composite-adjunction`: `CategoryTheory.Adjunction.comp`,
  `comp_unit_app`, `comp_counit_app`, `comp_homEquiv`, and `Adjunction.id`,
  `Mathlib.CategoryTheory.Adjunction.Basic`.
- `lem-weil-pbc-conjugate-iso-unit-equation`:
  `CategoryTheory.unit_conjugateEquiv_symm` and `conjugateIsoEquiv`,
  `Mathlib.CategoryTheory.Adjunction.Mates`; the identity-right-adjoint case
  `Adjunction.leftAdjointUniq` and `unit_leftAdjointUniq_hom_app` was also read
  in `Mathlib.CategoryTheory.Adjunction.Unique`.
- `def-weil-pbc-adjunction-conjugate`: `CategoryTheory.conjugateEquiv` and
  `conjugateIsoEquiv`, `Mathlib.CategoryTheory.Adjunction.Mates`.

Source check: the current blueprint's
`sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp.md`
names this exact theorem in its Lean front matter and states this exact equality.
Its proof file describes the same unit/conjugation/associativity calculation.
The DAG makes the inverse orientation explicit; the published construction was
checked directly rather than inferred from the name or an older docstring.

Edge cases: identity morphisms remain allowed, with the existing sibling
`condensedPushforwardHom_id` identifying the result with `lowerStarId.inv`;
there is no strict-identity assumption on chosen pullbacks. Empty schemes and
morphisms from them are included. No nonzero or commutative ring hypothesis is
used. All scheme universes are arbitrary `u`, and the pro-étale sheaf coefficient
universe is the framework's `Ab.{u + 1}` throughout. Neither site universe is
collapsed. All functors here are ordinary, not derived.

Searches (2026-10-18; exact tool results are in the sandbox's `searches.jsonl`):

- LeanFinder via `msearch.py`: “Composition of canonical coefficient unit maps
  into pushforwards of sheaves pulled back from a point”; eight results, including
  `SheafOfModules.unitToPushforwardObjUnit` and related module-sheaf maps. None is
  this pro-étale coefficient theorem.
- LeanSearch via `msearch.py`: “Composition of canonical coefficient unit maps
  for inverse image and direct image of sheaves”; eight results, including
  `SheafOfModules.pullbackComp`, `pushforwardComp` and the unit-to-pushforward maps.
  These use a different category and do not replace the published theorem.
- Loogle via `msearch.py`: `CategoryTheory.unit_conjugateEquiv_symm`; one exact
  result, the generic unit equation already recorded by its dependency node.
- Mathlib grep via `msearch.py` in `CategoryTheory`:
  `condensedPushforwardHom|condensedPullbackHom|unit_conjugateEquiv`; four hits,
  the generic unit equation and its uses. No condensed coefficient theorem.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `condensedPushforwardHom|lem-sfb-eta-comp|upperStarFromPointComp|condensedPullbackHom`,
  and for `condensedPushforwardHom_comp|unitCompUpperStarComp_comp`: no matches
  in that older checkout. Search for the item id there likewise gave no match.
- `rg` in `lean/Sheaf` for the same names: existing consumers of the canonical
  coefficient maps and `ProfinitePointPullback`'s natural-isomorphism coherence
  statements, but no duplicate declaration of this exact equality.
- `rg` in the explicitly authorized `lean/WeilConjectures` framework found
  `ModuleObject/Basic.lean:469` declaring `condensedPushforwardHom_comp`.
  Its full signature, docstring and proof were read, then the current server
  source was obtained with `scompile.py --source` (now at line 657).
- `rg` of `dag/lean_names_upstream.json` for the declaration and item id: no
  entry; the current blueprint's front matter and published source supply the
  authoritative exact match.

No new nodes, dependency repairs, statement correction, or statement dispute.
The published theorem already has a proof; this delivery neither changes nor
adds any proof or definition. The scratch-only `ExistingChecks.lean` passed `scompile.py` with no errors or
warnings: the sandbox check took 11.7 seconds and the library confirmation
49.6 seconds, each under the 60-second limit. It printed the full theorem type
and defining constructions, confirming the parameter list and inverse orientation.
The delivery wrapper also checks the recorded existing declaration on the server.

## Second reading by Q28

Worker self-check, not an independent review: the dispatch brief forbids starting
other agents and assigns independent review to the maintainer. Reopened the item,
its ten dependency records, the blueprint statement and proof, and the published
signature and comparison construction. Every quantified morphism is arbitrary;
`condensedRingObj`, `condensedPushforwardHom`, and `lowerStarComp.hom.app` identify
all three maps and both endpoints. The inverse orientation in the expanded DAG
statement agrees with the actual `conjugateIsoEquiv` construction. The absence of
`MonObj` in the theorem's type is harmless: its equality concerns underlying
abelian sheaves and specializes to every ring object. No mismatch or edit beyond
the new existing-declaration record was needed.
