## Worker report

Repair of the returned immutable head `5af5e8924293`. I retained the saved packet and first ran `deliver2.py Q98 lem-asd-supported-kummer-scalar-source --no-push`: it passed compilation and preflight (dry-run commit `5c0b17fbd8`). That mechanical success did not address the independent review's mathematical objections. The changes below repair them. Comparison with the current shared node found no changes outside `lean` in the saved node, and no landed declaration for this item. The wrapper rebases the delivery onto the current `newtargets-dag` without direct git commands or writes to either read-only project.

The module `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource` defines the real ring map `supportedScalarMap` and states `supported_kummer_scalar_source` with `sorry`. It uses the existing ordinary unbounded module-derived scalar-unit predicate; it does not introduce another derived tensor or choose a comparison from a bare existence proposition. The ring `ULift (ZMod N)` is the canonical universe lift of Λ, with coefficient map `(Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom`.

Hypotheses, individually:

- A scheme T: `(T : Scheme.{u})`; the support is another scheme `{D : Scheme.{u}}`.
- A closed immersion: `(i : D ⟶ T) [IsClosedImmersion i]`.
- Integer N ≥ 1: `(N : ℕ) (hN : 1 ≤ N)`; positive integers are represented by this pair.
- Λ = Z/N: every Λ-module coefficient type is `ULift.{u + 1} (ZMod N)`; the lift only changes size.
- A finite commutative ring killed by N: `(A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)`.
- No hypothesis of coefficient flatness, invertibility of N on T, Cartier ideal, reducedness, or Noetherianness is present.

Clauses, individually, in the order they occur in Lean:

1. The existential `ηD` has source `ordinaryFiniteConstant Λ D` and target `Res (ordinaryFiniteConstant A D)`. Its first conjunct quantifies over **every** `U : D.Etaleᵒᵖ` and `r : ULift (ZMod N)` and fixes its value on the image of r under `toSheafify` to the image of `supportedScalarMap N A hA r`. Thus this is the coefficient unit Λ_D → A_D specified in the node. The sheafification universal property determines the map from these constant-presheaf images, including on locally constant sections.
2. `ηT` is similarly a map of ambient constant sheaves into restriction of scalars. The second conjunct fixes its value on every ambient constant-presheaf generator by the same formula. This fixes the ambient identification used for the final unit clause.
3. `SupportedDerivedScalarUnit ... D (ordinaryFiniteConstant Λ D) (ordinaryFiniteConstant A D) ηD` expresses derived scalar extension on D by its adjunction, with the now fixed unit. Its test objects range over the entire unbounded `DerivedCategoryModule A D`.
4. `SupportedDerivedScalarUnit ... T (lowerStar Λ i ... Λ_D) (lowerStar A i ... A_D) (...)` is the required canonical comparison `Ri_* Λ_D ⊗ᴸ A_T ≅ Ri_* A_D`. Its unit is exactly `(lowerStar Λ i).map ηD ≫ (lowerStarCompRestrictScalarsIso ... i).inv.app ...`. Finite direct image is exact, as in proof step 2, so these degree-zero sheaves are the canonical representatives of both derived direct images. The inverse comparison has source `i_* Res A_D` and target `Res i_* A_D`, as required. The predicate asserts the derived adjunction bijection for every derived A-object, so it specifies the actual value of derived extension, not an abstract isomorphism class.
5. The next `SupportedDerivedScalarUnit ... T Λ_T A_T ηT` fixes the ordinary constant unit as the ambient derived-extension unit. This is the ambient identification in the node's last clause.
6. The final equality is `ηT ≫ Res(supportedConstantUnit A i) = supportedConstantUnit Λ i ≫ i_*(ηD) ≫ comparison`. Both sides are maps Λ_T → Res(i_*A_D). Transposing by clause 5 identifies the scalar extension of Λ_T → i_*Λ_D with `supportedConstantUnit A i`. Exact direct image identifies this with the stated derived adjunction unit.
7. Validity without flatness is rendered by the absence of any flatness assumption throughout all the binders and all three derived universal properties. The proof plan uses the flat supported source rather than any resolution of A.

Dependency declarations read and used (existing modules; no dependency module is repaired):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms (`def-pc-scheme`).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion` (`def-weil-closed-immersion`).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the recorded node `def-weil-pbc-derived-categories`; I read the current source with `scompile.py --source` because it is absent in the older checkout. The same ordinary `DerivedCategoryModule` encoding is re-exported by the already imported `Sheaf.AlgebraicGeometry.DerivedCategories`; the signature of the existing scalar-unit predicate uses it.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and `upperStarLowerStarAdjunction` (`def-weil-pbc-direct-image`, `def-weil-pbc-inverse-image`).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`; its definition is sheafification of `Functor.const`, exactly as `def-weil-pbc-constant-sheaf` states.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `AlgebraicGeometry.Etale.derivedTensor` (`def-kun-derived-tensor`); the statement uses its adjunction characterization through the existing scalar-unit predicate.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: `SheafOfModules.derivedChangeOfRingsIndependentCoefficients` (`lem-pur-derived-change-of-rings`), with canonical computation on K-flat sources and independent site/coefficient universes.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar`: `AlgebraicGeometry.Etale.SupportedDerivedScalarUnit` (`def-asd-ordinary-supported-kummer-scalar`). Its full signature quantifies over all unbounded derived target objects, and its formula precomposes with the specified η after the exact restriction-of-scalars/single-functor comparison.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`: `AlgebraicGeometry.Etale.supportedConstantUnit` (`def-asd-ordinary-supported-kummer-boundary`), defined by the inverse-image/direct-image adjunction and the canonical constant comparison.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `AlgebraicGeometry.Etale.ordinaryFiniteConstant` (`def-asd-ordinary-finite-p1-kummer-class`), literally the constant sheaf at `ModuleCat.of A A`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `AlgebraicGeometry.Scheme.finiteEtaleTwistScalar` (`def-asd-finite-etale-tate-twist`), defined by `ZMod.castHom` from `hA`.
- `WeilConjectures.SixFunctors.BaseChange.RestrictScalars`, via `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar`: `AlgebraicGeometry.Etale.lowerStarCompRestrictScalarsIso`, the objectwise direct-image/restriction identification, defined as `Iso.refl`. This supplies the coefficient bookkeeping for direct image; it is not a new projection formula or a new mathematical hypothesis.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`: `CategoryTheory.Sheaf.restrictScalars`, composition with the existing module restriction-of-scalars functor, and its exactness instances.

The four helper-owning nodes `def-asd-ordinary-supported-kummer-scalar`, `def-asd-ordinary-supported-kummer-boundary`, `def-asd-ordinary-finite-p1-kummer-class`, and `def-asd-finite-etale-tate-twist` are now explicit `stmt_deps`, as permitted for already landed nodes. They supply only the indicated declarations: importing their broader Kummer definitions does not add their Cartier or invertibility hypotheses to this theorem. No node's natural-language statement, proof, or proof dependencies changed.

The theorem docstring now contains all six proof steps of the node, with their node citations: normalized stalks of the finite closed support; exact direct image and derived representatives; K-flatness by tensor-stalk comparison and exact conservative stalks; the balanced section formula and stalkwise inverse for the scalar comparison; computation on the identity K-flat resolution; and the explicit unit calculation. Modules of the recorded proof dependencies are imported for the stage-3 proof. The helper `supportedScalarMap` also now has its source place and blueprint citation.

Edge cases checked:

- N = 1 forces A to be the zero ring from `hA`; both coefficient units and the comparisons reduce to zero-object maps. No nontriviality assumption excludes it.
- A = 0 works for every positive N.
- Empty D gives zero supported sheaves; the normalization on D is still quantified and automatically compatible with the empty site's zero sections.
- Identity i gives the ordinary coefficient unit and Λ ⊗ᴸ A = A. No proper-support condition appears.
- Λ = Z/4 and A = Z/2 is a genuinely nonflat coefficient change. The supported source has stalks Λ or zero, so the proof's K-flat computation still yields A or zero.
- Nilpotent closed thickenings have the same singleton-or-empty geometric-fibre calculation; no reducedness is used.
- The reviewer's sign example, N = 3 and A the lifted Z/3, with identity support over a geometric point: replacing both η maps by their negatives sends the generator one to minus one. Each of the two new normalization conjuncts requires one to go to one, so the negated pair no longer satisfies the statement. On any disconnected etale object the formula is imposed on all constant generators, and sheafification fixes their locally glued sections too.

Searches retained from the saved packet: `msearch.py ... leanfinder "derived scalar extension closed supported constant sheaf"` returned generic sheaf/locally constant results, no exact theorem; `msearch.py ... loogle "derivedTensor, lowerStar, upperStar, constantSheaf"` found no exact theorem (`derivedTensor` unknown to Loogle); `msearch.py ... grep "Kummer|supported|derivedChange|constant" WeilConjectures` found no exact statement. The saved `searches.jsonl` is retained. Project/upstream `rg` found the scalar-unit predicate, supported unit, ordinary constants, and canonical coefficient comparison already reused here. In this repair I searched `rg` for `supported_kummer_scalar_source|supportedScalarMap` in the named project and upstream Lean trees, and the item id in upstream Lean: no landed duplicate. I searched DAG nodes for `lowerStarCompRestrictScalarsIso`: no additional owner record, and read its actual upstream definition. I read the four helper node records and their recorded source declarations rather than introducing copies.

No new nodes, dependency repairs, natural-language statement correction, or statement dispute is required. The canonical-normalization equations repair the Lean rendering of the already canonical node statement.

## Second reading by Q98

This is the required second self-check with the node and revised file open; the maintainer performs the independent review. No other agent was started.

I reread the current blueprint `main-20261015/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/lem-amb-cartier-kummer-map.proof.md`, final paragraph: the derived scalar extension has source i_*A_D, as seen on stalks, without flatness. I also read Stacks `etale-cohomology.tex`, Proposition `proposition-finite-higher-direct-image-zero` (03QP) and Lemma `lemma-stalk-pullback` (03Q1), and the full six-step argument in this item's node. The node adds the precise canonical comparison and its unit compatibility. The Lean binders contain exactly a scheme, a closed immersion, positive N, and finite commutative A killed by N. In particular the support is not required to have invertible ideal and N is not required invertible on T.

I checked each clause a second time against its actual Lean expression. `ordinaryFiniteConstant` is the sheafification of the constant free rank-one module. The two `∀ U r` equations use precisely its sheafification unit and the existing canonical scalar map, for D and for T separately. The equations determine the maps: every morphism from a sheafification is determined by its composite with `toSheafify`. Thus simultaneous negation over Z/3 is excluded at r = 1; the original existential formulation failed this test. The three `SupportedDerivedScalarUnit` clauses all use these same fixed η maps, with no new independent morphism in the supported clause. On expanding the predicate, its quantified K ranges over the full unbounded derived A-category, and the displayed bijection is precisely derived scalar adjunction. Exactness of closed direct image gives the node's Ri_* representatives. Finally the equality's left side is ηT followed by restriction of the actual A-unit, and the right side is the actual Λ-unit followed by pushforward of ηD and the inverse objectwise scalar comparison. Their common target is Res(i_*A_D), so it is exactly the unit clause under that derived adjunction.

The changes required by the return are concrete:

- H3/H7: added generator normalization for both ηD and ηT. The node already demanded the canonical coefficient unit, so its statement is unchanged and no `statement_change` is appropriate.
- H8: added the helper's source/blueprint docstring, explicit citations of all four existing helper-owning nodes, and the six-step proof plan with the node's cited inputs. There is still exactly one theorem and its entire proof is `sorry`; the ring-map definition has real data.
- H11: replaced the automatically supplied placeholder with this reading, including the binders, all normalization and universal-property clauses, the final typed composite, and the counterexample check.

I rechecked the zero ring, N = 1, empty and identity support, nonflat Z/4 → Z/2, and nilpotent support against the binders and normalization formulas. None is excluded. Universes are explicit (`u`, coefficient carriers in `Type (u+1)`), and `autoImplicit false` is set. The helper declarations already exist and are reused, not privately copied. The node's `lean.statement` is copied verbatim from the revised declaration, including its line breaks, and `lean.declarations` lists both local declarations. There are no lines over 100 characters in the module. The revised file compiled cleanly through `scompile.py`; final delivery preflight is run after this report is saved.

Final validation: the repaired packet passed `deliver2.py Q98 lem-asd-supported-kummer-scalar-source --no-push` at dry-run commit `d09b642fb7`, including the current server preflight and clean per-file compilation. The actual push uses the same prescribed wrapper and revalidates against its current base.
