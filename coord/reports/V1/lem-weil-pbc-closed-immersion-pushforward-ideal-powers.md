## Worker report

The module Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers states
AlgebraicGeometry.Scheme.closedImmersion_pushforward_idealPowers, with one sorry.
No new definition, dependency module, or statement correction is needed.

Each hypothesis and clause:

- Schemes and morphism: `{X Z : Scheme.{u}} (i : Z ⟶ X)`; closed immersion:
  `[IsClosedImmersion i]`. The ideal J of i is the canonical `i.ker`, not extra data.
- Quasi-coherent ideal I: `I : X.IdealSheafData`. Its extension is the dependency's
  `I.comap i`. No private definition of extended ideals or pullback is introduced.
- (1), quasi-coherence: `(I.comap i).toModules.IsQuasicoherent`.
- (1), affine formula: every `U : X.affineOpens` has an affine `V` with
  `hV : V.1 = i ⁻¹ᵁ U.1`, and `(I.comap i).ideal V` is the `Ideal.map` of
  `I.ideal U` through `i.appLE U.1 V.1 ...`. Under the canonical quotient description
  of a closed immersion this is I(U)(R/J(U)), exactly the node's formula.
  The hV proof passed to appLE merely transports the equality of opens. The quotient
  identification is the one already guaranteed by the closed immersion; it is not
  an additional hypothesis or additional conclusion.
- (2): all quasi-coherent G and all n with `1 ≤ n` are quantified. The two
  `Subobject.mk (image.ι ...)` terms compare the pushforward of the upstairs product
  inclusion and the downstairs product inclusion in the same object i_*G. Taking
  images expresses subobjects without requiring separately registered Mono instances
  for the shared ideal-power inclusion definition. Closed-immersion pushforward is
  left exact, so the first image is precisely the pushforward submodule in the node.
- (3), induced isomorphism: a single family ρ indexed by every quasi-coherent G and
  every positive n compares `formalModuleQuotient I n (i_*G)` with
  `i_* (formalModuleQuotient (I.comap i) n G)`. The first equation says its hom
  composed after the downstairs projection is the pushforward upstairs projection,
  so it specifies the induced map rather than an arbitrary object isomorphism.
- (3), naturality: for every linear u between quasi-coherent G and H, the quotient
  map of i_*u followed by ρ_H equals ρ_G followed by i_* of the quotient map of u.
  `formalModuleQuotientMap ... (Nat.le_refl n)` supplies these canonical maps.
- (3), levels: the last square commutes for `h : n ≤ m` and `hn : 1 ≤ n`.
  `formalModuleQuotientMap ... (𝟙 G) h` is reduction from m to n; `le_trans hn h`
  supplies positivity of m. There is no extra condition on the levels.

Dependency declarations read (full definitions/signatures and docstrings):

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Spec, Spec.map (schemes,
  morphisms, spectra and the interpretation of affine opens).
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion (closed
  embedding and surjective stalk maps).
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: Scheme.Hom.ker, ker_apply (canonical
  ideal of i, affine-section kernel).
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial: Scheme.IdealSheafData.comap,
  extended ideal defined as the kernel of the base-changed closed subscheme.
- Sheaf.AlgebraicGeometry.TensorPullback: Scheme.Modules.tensorPullback. Its tensor
  definition and full signature were read. The statement uses the direct image from
  Mathlib.AlgebraicGeometry.Modules.Sheaf, Scheme.Modules.pushforward; the dependency's
  extended-ideal notion already packages the image of the pullback multiplication.
- Sheaf.AlgebraicGeometry.CoherentFormalModule: formalModuleQuotient,
  formalModuleQuotientπ, formalModuleQuotientMap; its imported shared
  Scheme.idealModuleProductι and Scheme.idealSheafPower from IdealModuleProductStalk.
  The quotient definitions are available without the Noetherian hypothesis needed
  for the category of coherent formal systems.
- Sheaf.AlgebraicGeometry.Coherent: its pqf-def-coherent docstring uses the existing
  Mathlib SheafOfModules.IsQuasicoherent for quasi-coherence. RingedSpace.IsCoherent
  is not a hypothesis here. This module is imported transitively.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module: toModules, toModulesι,
  realizes IdealSheafData as an actual ideal submodule. Imported transitively.

Edge cases checked: I = 0 gives zero products and identity quotient comparisons;
I = O_X gives all of G as positive products and zero quotients. Empty schemes and
empty inverse images are allowed. n = 1 is included and n = 0 excluded exactly as
in the node. m = n is allowed. All commutative section rings and characteristics
are allowed. No Noetherian, coherent, finite-type, separatedness or nonempty hypothesis
was added. The scheme and module universes use the shared standard u.

Sources opened: Stacks tag pages https://stacks.math.columbia.edu/tag/088A,
https://stacks.math.columbia.edu/tag/01QO and https://stacks.math.columbia.edu/tag/01QY.
The local tex checkout is absent. 088A's proof identifies closed-subscheme adic systems;
01QO provides affine quotient descriptions and 01QY exact quasi-coherent direct image.

Searches made:

- msearch.py leanfinder: "Pushforward along a closed immersion commutes with multiplication
  by powers of an extended ideal and quotient modules". Eight hits, including ideal
  quotient transitions, IdealSheafData.map_comp, Submodule.factorPow/factorPowSucc;
  no sheaf-module-power equality or natural quotient comparison.
- msearch.py leansearch: "Closed immersion pushforward quotients by powers of ideal sheaf".
  Service unavailable, Internal Server Error. Logged as unavailable, without a verdict.
- msearch.py loogle: "AlgebraicGeometry.Scheme.Modules.pushforward,
  AlgebraicGeometry.IsClosedImmersion". No hits.
- msearch.py grep: "pushforward.*ideal|ideal.*pushforward", AlgebraicGeometry.
  Six hits on ideal sheaf direct image and spectrum stalk maps; no module-power theorem.
- Local rg/grep of WeilConjectures for the node id and pushforward/ideal keywords:
  ideal-sheaf functoriality and affine ideal pushforward only; no exact declaration.
- Local rg of lean/Sheaf: AffinePushforwardIdealProduct gives a single product equality,
  not this combination of powers, affine image formula, quotient isomorphisms and
  compatibility. IdealTimesQuasiCoherentAffineSections gives affine product formulas.
  Both modules were read; neither duplicates this statement.
- rg for closedImmersion_pushforward_idealPowers in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no name collision.

Validation: the server single-file compilation passed with no warnings. Every theorem
proof is sorry. The docstring gives the node's nine proof steps for stage 3.

## Second reading by V1

I read the node statement, its source place (Stacks coherent.tex, proof of Lemma 088A,
lines 6961--6968, with Morphisms Lemmas 01QO and 01QY), and the Lean declaration
`AlgebraicGeometry.Scheme.closedImmersion_pushforward_idealPowers` independently.
The item-by-item rendering is:

- The schemes `X Z : Scheme.{u}`, morphism `i : Z ⟶ X`, and instance
  `[IsClosedImmersion i]` are the first binders.  This is exactly the node's closed
  immersion and introduces no Noetherian, finite-type, separatedness, or nonempty
  hypothesis.
- The quasi-coherent ideal `I : X.IdealSheafData` is the node's `𝓘`; its extended
  ideal is the recorded `I.comap i`, with no private replacement.  The imported
  `toModules`, `idealSheafPower`, `idealModuleProductι`, and
  `formalModuleQuotient` declarations are the dependency notions for products,
  powers, and quotients.
- Clause (1) is the conjunction `(I.comap i).toModules.IsQuasicoherent` followed by
  the affine-open formula.  For every `U : X.affineOpens`, the existential `V` and
  `hV : V.1 = i ⁻¹ᵁ U.1` state the affine inverse image, and the equality using
  `(I.ideal U).map (i.appLE ...).hom` is the image of `I(U)` in the quotient section
  ring.  The proof argument to `appLE` only transports `hV`; it is not an extra
  hypothesis.
- Clause (2) quantifies every quasi-coherent `G : Z.Modules` and every natural
  `n` with `1 ≤ n`.  Equality of the two `Subobject.mk (image.ι ...)` terms is
  equality of the pushforward of the upstairs product inclusion and the downstairs
  product inclusion as subobjects of the same `(Modules.pushforward i).obj G`, exactly
  the stated equality of submodules.
- Clause (3) existentially supplies one family `ρ`, indexed by all such `G,n`, of
  isomorphisms between the two formal quotients.  The first conjunct fixes the map by
  the quotient-projection equation; the second gives naturality for every linear
  `u : G ⟶ H`; the third gives the level square for `n ≤ m` and `1 ≤ n`, with
  `le_trans hn h` supplying positivity of `m`.  Quantifier order and composition
  directions agree with the node.

Edge cases were checked: `n = 1` is included and `n = 0` excluded; `m = n` is
allowed; zero and unit ideals reduce to the expected zero/full products and quotient
cases; empty schemes and empty inverse images are permitted; no characteristic,
Noetherian, coherence, finite-type, separatedness, or nonemptiness assumption is
introduced; the shared universe `Scheme.{u}` does not exclude the node's cases.

I repeated the existing-definition searches: local `rg` over `WeilConjectures/` and
`lean/Sheaf`, grep of Mathlib's IdealSheaf and Modules files, and the recorded
LeanFinder/Loogle/LeanSearch queries.  They find only the dependency notions
(`IdealSheafData.comap`, pushforward, affine ideal maps, and quotient infrastructure),
not this combined theorem.  Thus no existing declaration or duplicate notion exists.

No mismatch was found.  The worker's module already compiles cleanly with
`scompile.py`; I made no source change.  The node's `lean.statement` remains verbatim
the theorem signature, and the theorem has only the permitted `sorry` proof.
