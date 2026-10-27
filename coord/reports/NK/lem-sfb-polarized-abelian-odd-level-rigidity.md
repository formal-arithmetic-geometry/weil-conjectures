## Worker report

The item is stated by `AlgebraicGeometry.polarized_abelian_odd_level_rigidity` in
`Sheaf.AlgebraicGeometry.AbelianVariety.PolarizedOddLevelRigidity`.
The theorem proof is `sorry`; the point-map helper has actual data.
No source statement is corrected. The current base item has no Lean record.
This repair changes the Lean code and node packet, addressing the immutable-head return.

Clause-by-clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The abelian variety is `A : Over (Spec (.of k))` with `[GrpObj A]` and
  `[IsAbelianVariety A]`, using exactly the dependency's existing class.
- The polarization is parametrized by its inducing ample invertible sheaf:
  `L : A.left.Modules`, `[Scheme.Modules.IsInvertible L]`, `hL : IsAmple A.hom L`.
  The node explicitly defines a polarization over this field as one induced by such an L.
  Thus quantifying over inducing L covers every polarization and imposes no extra condition.
  Multiple L inducing the same polarization yield the same point map and preservation condition.
  No principal-polarization assumption is present: the principal sentence defines terminology,
  not an assumption of the theorem.
- `GrpObj.mulLeft A x` is the existing group-scheme left translation, constructed from
  the constant map x and the identity by group multiplication. No translation is redefined.
- `abelianPolarizationPointMap A (Scheme.Pic.ofIsInvertible L) x` is
  `Pic.map (t_x).left [L] / [L]`, exactly `[t_x^*L tensor L^{-1}]`.
  The division is the tensor product with the dual in the existing Picard group.
- The group automorphism is `a : A ≅ A`, `[IsMonHom a.hom]`. Its inverse is automatically
  a group homomorphism. Being in Over says it is a k-scheme automorphism.
- `hpolarization` says `a^*(phi_L(a(x))) = phi_L(x)` for every rational point x.
  Duality is pullback on Pic^0, as the node says, so this is the exact formula
  `a^vee lambda a = lambda` in the ambient Picard group. This tests a morphism identity,
  not only a weaker abstract action: over algebraically closed k the smooth A is reduced,
  all closed points are k-rational and dense, and A^vee is separated. The inclusion of
  Pic^0 into Pic is injective. Consequently this pointwise identity is equivalent to the
  stated morphism identity. The universal dual/Poincare construction is not needed to type
  this equivalent expression of preservation. No arbitrary substitute for lambda is used.
- `(n : ℕ) (hn : 3 ≤ n)` represents the integer n ≥ 3; negative integers are irrelevant
  under that inequality. `hchar : IsUnit (n : k)` is precisely invertibility in k.
- `hlevel` quantifies over every k-point `x : 𝟙_ (Over (Spec (.of k))) ⟶ A` and assumes
  `x ≫ (𝟙 A ^ n) = 1`. The recorded group-scheme module defines `[n]` as that power
  in the pointwise group on morphisms; `1` is the identity point (zero additively).
  Its conclusion `x ≫ a.hom = x` is exactly triviality on A[n](k).
- `a = Iso.refl A` is equality as an actual k-scheme automorphism.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`.
  The algebraic-closure node's mathlib_match explicitly lists the latter notion.
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs: `IsAbelianVariety`.
- WeilConjectures.AlgebraicGeometry.Modules.VeryAmple: `IsAmple`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: `Scheme.Modules.IsInvertible`.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`; Cartesian.Mon: `IsMonHom` and
  the pointwise multiplication on Hom, inherited through GroupScheme.Defs.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: `torsionSubgroupScheme` is the
  kernel of `𝟙 A ^ n`, matching the level predicate used here.
- WeilConjectures.AlgebraicGeometry.PicardFunctor and Picard.Group: `Scheme.Pic`,
  `Scheme.Pic.map`, `Scheme.Pic.ofIsInvertible`, and the existing tensor-product group law.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Basic: `GrpObj.mulLeft`, reached through
  the added existing dependency `def-sc-group-scheme-translate`.
- The point map is an item-module helper listed in `lean.declarations`, with the item
  blueprint citation; `def-sc-picard-group` is also added to the statement dependencies.
- All four proof dependencies have no usable Lean records on the base; they are named in
  the proof docstring and need no imports yet.

Edge cases: dimension zero is included; the zero-dimensional abelian variety has the
identity automorphism. n may be even (e.g. 4) and composite (e.g. 9); there is no oddness
or primality assumption. Characteristic zero and positive characteristic prime to n are
included. In characteristic dividing n the required IsUnit fails, as intended.
n = 0, 1, 2 are excluded by hn; n = 2 would fail for [-1] on positive-dimensional A.
Automorphisms fix the group identity, so translations are not accidentally allowed.
The empty scheme is not an abelian variety under the recorded ConnectedSpace convention.
Universes use one explicit u for the field and its schemes, as the existing definitions do;
no independent universe makes point quantification vacuous. Pic itself lives in u+1.

Searches (actual msearch.py results and local rg, no duplicate found):

- leanfinder: `An automorphism of a polarized abelian variety fixing all n torsion points for n at least three invertible in the field is the identity` — 8 hits, all cyclotomic-character declarations: modularCyclotomicCharacter.id, .unique, modularCyclotomicCharacter'.unique', .aux, .toFun_unique', cyclotomicCharacter.spec, modularCyclotomicCharacter.toFun_unique, .spec. No abelian polarization point map.

- loogle: `IsAbelianVariety, polarization` — 0 hits; unknown identifier IsAbelianVariety.

- leansearch: `An automorphism preserves the polarization induced by an ample line bundle if pullback fixes the translation difference classes in the Picard group` — 8 hits: CommRing.Pic.mapRingHom_id, RootPairing.PolarizationIn.congr_simp, RootPairing.polarizationEquiv_toLinearMap, RootPairing.Equiv.instMulActionAut, QuadraticForm.polarBilin_baseChange, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom, RootPairing.PolarizationEquiv. Ring Picard pullback and root-system polarizations do not define the abelian-variety point map.

- grep: `msearch grep polariz|[Dd]ual[Aa]belian AlgebraicGeometry; rg abelianPolarizationPointMap|abelianTranslation in Mathlib, WeilConjectures and Sheaf; rg polarization|dual abelian in DAG; blueprint_refs.py search polarization` — msearch 0 hits. No matching polarization point-map declaration in Mathlib or either project library.
  The original search missed the existing translation `GrpObj.mulLeft`; this repair uses it. DAG lem-sfb-abelian-polarization-calculus states representability and identities but has no Lean declaration or definition interface; no definition node gives the point map. Blueprint search: 0 nodes. Existing Scheme.Pic, Scheme.Pic.map and group-object multiplication are reused.

Additional searches: rg of the item id in WeilConjectures returned no declaration;
rg polarization/dual abelian in WeilConjectures found only unrelated projective duality;
Sheaf contained polarized scheme descent and the downstream geometric-curve theorem,
not an abelian polarization point map. The DAG has the unstated theorem
lem-sfb-abelian-polarization-calculus about full representability and identities; it does
not provide a definition interface and is not duplicated as a theorem here.
The source PDF was read with pdftotext: I Section 11 p.53 and Proposition 14.4 p.62,
with its proof and Lemma 14.5 p.63. The source.place p.51 in the item appears stale;
the polarization convention is actually p.53. This does not affect the statement.

## Repair of return at f5ddefc6aa98

- A6: the previous re-push changed only the report. This packet substantively changes the
  item module and node, and removes the extra definition node and its module. It is not an
  unchanged rebase or re-push of f5ddefc6 / 8c56cca9.
- H12: removed `def-sfb-abelian-polarization-point-map.json` and
  `PolarizationPointMap.lean`. The helper `AlgebraicGeometry.abelianPolarizationPointMap`
  now belongs to the item module and is listed with the theorem in `lean.declarations`.
  The statement dependencies are exactly the current base list plus the already recorded
  `def-sc-group-scheme-translate` and `def-sc-picard-group`, as the return requests.
  No reachability flags, ancestor nodes or downstream citers are changed.
- H4: removed `abelianTranslation` and its literal group-law construction. The helper body
  is now `Scheme.Pic.map (GrpObj.mulLeft A x).left L / L`, using the existing translation
  from the publicly imported `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`.
- Advisory: the polarization convention is at printed p.53. This is documented here and
  in the helper source citation; the inherited `source.place` p.51 is preserved because
  the permitted node delta is `lean` and the requested statement dependencies.

Compared with the current read clone, only `lean` and `stmt_deps` of the item differ;
there is now one delivered module and one delivered node. The theorem signature and
mathematical content are unchanged from the version the return found correct.
The required initial dry run on the retained packet passed (`410365c9bd9`), but that
packet still had the return's defects, so it was repaired before delivery.

## Validation

The repaired module compiled through scompile.py in both sandbox and library module
contexts (2.4 s and 2.3 s), with no errors or warnings. The repaired packet passed
deliver2.py --no-push at dry-run commit `47f79c5ebd5`, including preflight and compile.
Self-check confirmed one node and one module, the verbatim theorem signature in
lean.statement, both declarations recorded, real helper data, exactly one theorem
sorry, all Lean lines at most 100 characters, and indent-1 UTF-8 JSON with final newline.
This report is the worker's self-check; independent review belongs to the maintainer.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
