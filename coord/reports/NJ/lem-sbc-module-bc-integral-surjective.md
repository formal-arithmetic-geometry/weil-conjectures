## Worker report

The source checkout already contains the exact arbitrary-coefficient theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` (lines 141--146).
Following the one-definition-per-notion rule, this delivery adds no Sheaf module and records
that declaration as `existing: true` in the item's node.  The theorem's proof is already in
the source; this statement delivery does not add a proof or a private copy.

The node's objects and clauses render as follows in the existing signature:

- `Λ : Type (u + 1)` with `[CommRing Λ]` is the arbitrary commutative coefficient ring;
  `p : X ⟶ S` is an arbitrary scheme morphism (the scheme dependency is Mathlib's
  `AlgebraicGeometry.Scheme`), and `q : ℤ` with `(hq : 1 ≤ q)` is the positive degree.
- `(hprev : Etale.BaseChangeProperty Λ p (q - 1))` is the fixed-base, single-degree
  `BC(p, Λ, q-1)` property recorded by `sk-def-bc`; it is not the universal property.
- `[QuasiCompact g] [QuasiSeparated g]` are exactly the qcqs assumptions on
  `g : T ⟶ S`.  The two Cartesian squares are the supplied `IsPullback` witnesses
  `sq : IsPullback e h g p` and `sq' : IsPullback e' h' (π ≫ g) p`, with the displayed
  projections and `π : T' ⟶ T`.
- `[IsIntegralHom π]` and `hπ : Function.Surjective π.base` render integral and surjective
  `π`.  The latter is the underlying-topological surjectivity from
  `def-weil-surjective-morphism`.
- `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` is a sheaf of Λ-modules on
  `T_et`; `((π)^*[ModuleCat.{u + 1} Λ].obj F)` is the recorded inverse-image sheaf `F'`.
  The hypothesis `hF` is `IsIso` for the canonical degree-q map over `π ≫ g`, and the
  conclusion is `IsIso` for the canonical degree-q map over `g`, exactly the two clauses
  of the node.  `baseChangeHomologyMap` is the degree-q homology of the canonical derived
  base-change morphism applied to F in degree zero.

The dependency declarations were read in full: Mathlib `Scheme`; `IsIntegralHom` and
`Surjective`; `ChosenCartesianSquare` as the project's cartesian-square interface;
`Etale.BaseChangeProperty`/`baseChangeHomologyMap`; and the source's `upperStar` inverse
image and `lowerStar` direct image.  The source theorem uses the categorical `IsPullback`
form of the same cartesian-square notion, with no extra finiteness, noetherian, torsion,
characteristic, or invertibility hypothesis.  The fixed universe convention
`Scheme.{u}` and `Λ : Type (u+1)` is the project's coefficient/site convention and does
not remove any mathematical case.

Edge cases checked against the signature and source: `q = 1`; `q ≤ 0` is allowed by the
underlying base-change definitions but the theorem correctly requires `q ≥ 1`; the zero
ring, zero sheaf, identity π, empty schemes, and empty test scheme are all admitted; no
nonempty, finite, torsion, or characteristic condition is added.  Dropping surjectivity
would make the stalk-unit step fail, so it is correctly retained.

## Second reading by NJ

I independently reread the node, Stacks Tag 0F04 (the lemma and proof at
`literature/stacks-project/etale-cohomology.tex` lines 16939--16994), the source theorem,
and every statement dependency.  The source lemma assumes `q ≥ 1`, fixed-base `BC` in
degree `q-1`, qcqs `g`, an integral surjective test replacement, and the two Cartesian
squares; its conclusion is exactly descent of the degree-q base-change isomorphism.  The
Lean theorem has each of those hypotheses in the same order and keeps arbitrary
commutative Λ without an integer-annihilator or invertibility assumption.

No mismatch was found.  The source's `(π)^*` notation is precisely `Etale.upperStar`,
the recorded inverse-image declaration; `IsPullback` is the categorical rendering of the
node's cartesian squares.  The `hF` premise and final `IsIso` conclusion use the canonical
`baseChangeHomologyMap` named by `sk-def-bc`, so neither endpoint nor map is weakened or
strengthened.  No statement correction, dependency repair, or new node is needed.

Searches performed with the required `msearch.py` wrapper and direct repository searches:

- LeanFinder query “integral surjective etale cohomology base change map isomorphism
  arbitrary commutative ring”: eight hits about étale permanence and base change, no
  higher-direct-image theorem.
- Loogle query `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`:
  zero hits because the source declaration is outside the Loogle index.
- Grep query `isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`: no Mathlib hit;
  direct `rg` found the exact source declaration and its consumers in the source checkout
  and shared project.
- Direct `rg` searches over Mathlib, `WeilConjectures/`, and `lean/Sheaf/` found no second
  declaration of the current arbitrary-Λ statement; the only related Sheaf declaration
  is the older torsion `ZMod n` theorem for the distinct node
  `sbc-lem-bc-integral-surjective`.

The only change in this second reading is attaching the exact existing source declaration
in the node's `lean` field (`existing: true`); no Lean file is written.
