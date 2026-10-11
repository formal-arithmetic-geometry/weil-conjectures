## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings` states
`AlgebraicGeometry.Scheme.Modules.quasiCoherent_algebra_changeOfRings`, with `sorry`.
It introduces no definitions and changes no mathematical statement or dependency.

Hypothesis and conclusion correspondence:

- The scheme Y is `(Y : Scheme.{u})`.
- The commutative algebra sheaves B and C are `(B C : Y.toTopCat.Sheaf CommRingCat.{u})`.
  Their algebra structures are the ring-sheaf maps `b : Y.sheaf ⟶ B` and
  `b ≫ φ : Y.sheaf ⟶ C`. Giving these maps into commutative rings is precisely
  giving their structure-sheaf algebra structures.
- The algebra morphism is `(φ : B ⟶ C)`. Because C's structure map is `b ≫ φ`,
  this is an O_Y-algebra morphism. No independent C structure map is needed;
  it would be forced to equal this composite by algebra-linearity.
- The underlying O_Y-modules of B and C are the rank-one self-modules
  `SheafOfModules.unit (𝓡 B)` and `SheafOfModules.unit (𝓡 C)`, restricted along
  `𝓻 b` and `𝓻(b ≫ φ)` respectively. The assumptions `hB` and `hC` assert
  exactly their quasi-coherence.
- The B-module P is `(P : SheafOfModules.{u} (𝓡 B))`; `hP` asserts that its
  restriction along `𝓻 b` is quasi-coherent as an O_Y-module.
- The change of rings is the dependency's `SheafOfModules.changeOfRings φ P`.
  Its definition sheafifies `SheafOfModules.changeOfRingsPresheaf φ P` as a
  C-module, not an abstract left adjoint.
- The first conclusion restricts this C-module along `𝓻(b ≫ φ)` and asserts
  `IsQuasicoherent`, exactly the specified underlying O_Y-module conclusion.
- The second conclusion quantifies over every `W : Y.Opens` with `IsAffineOpen W`.
  `Function.Bijective` is applied to the component at `op W` of the
  `PresheafOfModules.sheafificationAdjunction` unit on the change-of-rings
  presheaf. This is the prescribed sheafification map t_W, with its actual
  sectionwise tensor-product domain and the sections of the prescribed sheaf.

The existing change-of-rings convention writes the section tensor as
C(W) tensor_{B(W)} P(W), with the target-ring factor first. The node writes
P(W) tensor_{B(W)} C(W). Canonical tensor symmetry sends p tensor c to
c tensor p, and identifies both the presheaves (including restrictions) and
sheafification maps. Bijectivity of the recorded map is thus exactly the
node's bijectivity assertion. This uses the existing notion without duplicating it.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, the recorded
  declaration of `def-pc-scheme`; `Mathlib.AlgebraicGeometry.AffineScheme`
  supplies `AlgebraicGeometry.IsAffineOpen`.
- `Sheaf.AlgebraicGeometry.Coherent`, recorded by `pqf-def-coherent`: its
  documentation expressly uses Mathlib `SheafOfModules.IsQuasicoherent` for
  the quasi-coherent clause. That clause, not its separate `RingedSpace.IsCoherent`
  definition, is needed here and used unchanged.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` and `unit`,
  using the Mathlib match of `def-weil-sheaf-of-modules-category`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`, recorded by
  `def-pur-sheaf-tensor-product`: `SheafOfModules.changeOfRings` and
  `changeOfRingsPresheaf`, with their full definitions read.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (changes the action, not the underlying sheaf).
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafificationAdjunction` and its unit, already imported
  through the tensor dependency. Its underlying abelian map is `toSheafify`.

Edge cases checked mathematically before writing: the empty scheme and empty
open are allowed (their section modules are zero and the map is bijective);
zero P and the zero C algebra give zero tensor products; identity change of
rings has the original quasi-coherent module and the affine section formula;
no flatness, finiteness, Noetherian, separation or characteristic assumption is
introduced. The maps and sheaves are in arbitrary explicitly bound universe u;
there are no test-object quantifiers with smaller independent universes.

Searches (2026-10-11):

- `msearch.py ... leanfinder "Extension of scalars along quasi-coherent sheaves
  of algebras preserves quasi-coherence and tensor sections on affine opens"`:
  eight hits, including `ModuleCat.tilde`, `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.QuasicoherentData` and `Scheme.Modules.map_smul`; no matching theorem.
- `msearch.py ... loogle "SheafOfModules.restrictScalars,
  SheafOfModules.IsQuasicoherent"`: zero hits.
- `msearch.py ... grep "changeOfRings|extendScalars"
  Algebra/Category/ModuleCat/Sheaf`: only the presheaf ChangeOfRings import.
- `rg` of the source `WeilConjectures` and the project's `lean/Sheaf` for
  `changeOfRings|quasi.*[Cc]hange|algebra.change.of.rings`: the project's tensor
  definitions and affine-module-correspondence citer, but no existing statement.
  Source matches are unrelated geometric base changes.
- `grep -rn` for the exact node id in the source: no matches.
- `rg` for the proposed full declaration's final name in Mathlib, the source,
  the project's Lean and `dag/lean_names_upstream.json`: no matches.

Source checked directly at https://stacks.math.columbia.edu/tag/01SB (proof's
change-of-rings assertion) and https://stacks.math.columbia.edu/tag/01I8 (1),
including the canonical section tensor map and its stalk argument. The local
Stacks tex files are absent on this machine. The complete seven-step DAG proof
is rendered in the declaration docstring, with its named dependency nodes.

Validation: server single-file compilation initially found a whitespace style
warning at the notation applied to `b ≫ φ`; the spacing was corrected. Final
server compilation is clean. `deliver2.py K1
lem-weil-pbc-quasi-coherent-algebra-change-of-rings --no-push` printed OK:
compilation and preflight passed except for the independent second-reading
section, which the second reader supplies. Nothing was pushed.
No statement dispute, dependency fault, or new node was needed.

## Second reading by K1

I independently read the sandbox node and module, all four statement dependency
nodes, the recorded Coherent and TensorProduct modules, and Mathlib's Scheme,
IsAffineOpen, SheafOfModules, unit, restrictScalars, IsQuasicoherent and
sheafificationAdjunction declarations. No new nodes or dependency modules are
in this delivery. There is no statement_change and no correction to review.

Source reading: local Stacks tex is absent, so I read the corresponding raw
Stacks master morphisms.tex and schemes.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/ and the tag pages
https://stacks.math.columbia.edu/tag/01SB,
https://stacks.math.columbia.edu/tag/01I8 and
https://stacks.math.columbia.edu/tag/01LA. At lemma-affine-equivalence-modules,
the change-of-rings assertion occurs in the construction of the quasi-inverse;
the affine morphism in that surrounding lemma is not a hypothesis on this
abstract change-of-rings assertion. At lemma-widetilde-constructions item (1),
the ring and modules are arbitrary; finite presentation is only imposed in
item (3), which is not used. Section section-quasi-coherent starts with an
arbitrary scheme and explicitly lists tensor and cokernel closure. Thus no
Noetherian, flatness, finiteness or separation assumption is missing here.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. Scheme Y: `Y : Scheme.{u}`; Mathlib's locally affine locally ringed space.
2. Sheaves of commutative O_Y-algebras B,C:
   `B C : Y.toTopCat.Sheaf CommRingCat.{u}`, with `b : Y.sheaf ⟶ B`
   and structure map `b ≫ φ` for C. A map from O_Y into a commutative
   ring sheaf supplies precisely its O_Y-algebra structure.
3. Algebra morphism φ: `φ : B ⟶ C`; compatibility with O_Y is encoded
   by the composite structure map. Conversely any compatible pair of
   structure maps has this composite, so no cases are lost.
4. Underlying modules of B,C quasi-coherent: `hB`, `hC` apply
   `IsQuasicoherent` to the respective `unit` self-modules after
   `restrictScalars (𝓻 b)` and `restrictScalars (𝓻(b ≫ φ))`.
   Mathlib unit is the ring itself as a rank-one module, and
   restrictScalars retains the abelian sheaf while changing the action.
   Coherent's docstring identifies exactly this Mathlib quasi-coherence
   notion with the dependency's affine-local scheme formulation.
5. B-module P: `P : SheafOfModules.{u} (𝓡 B)`; its semilinear restrictions
   and sheaf property are part of that dependency's Mathlib carrier.
6. Underlying O_Y-module of P quasi-coherent: `hP` is
   `((restrictScalars (𝓻 b)).obj P).IsQuasicoherent`.
7. Specified extension of scalars: `changeOfRings φ P`, whose dependency
   definition is sheafification of `changeOfRingsPresheaf φ P`. The latter
   has section objects `ModuleCat.extendScalars (φ.hom.app U).hom` and
   restriction maps characterized on pure tensors. It is not a substitute
   abstract left adjoint or an arbitrary object.
8. First conclusion: restrict that C-module along `𝓻(b ≫ φ)` and assert
   `IsQuasicoherent`. This is precisely the underlying O_Y-module.
9. Every affine open W: `∀ (W : Y.Opens), IsAffineOpen W → ...`.
   It includes all affine opens, without an additional chosen cover.
10. Bijectivity of t_W: `Function.Bijective` of the unit component of
    `PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C).obj)` on
    `changeOfRingsPresheaf φ P`, evaluated at `op W`. Mathlib's
    `toPresheaf_map_sheafificationAdjunction_unit_app` identifies the
    underlying map with `toSheafify`, so this is the prescribed map,
    rather than existence of some bijection between section types.

The factor order deserves a check: the dependency uses C(W) tensor_B(W) P(W).
The natural symmetry p tensor c ↦ c tensor p identifies the node's presheaf
with this one: both restrictions send the factors to their restrictions.
Sheafifying this natural isomorphism and applying naturality of the unit
identifies the two section maps. Both the symmetry and its sheafification are
isomorphisms, so bijectivity of the displayed unit component is exactly
bijectivity of the node's t_W. This is the existing dependency's convention,
not a new notion or a weakening.

Edge cases: the empty scheme and empty affine open are admitted; sections
there are singleton zero modules. P = 0 and the zero C algebra are admitted
and yield zero tensors. The zero B algebra forces a unital target C and P to
be zero, also admitted. Identity φ and arbitrary characteristics are covered.
There is no index set or degree n in this statement. All occurrences of u
are explicitly bound; no hidden smaller-universe quantifier occurs. Any
scheme/rings/modules can be placed in one common larger universe, so the
shared universe is no mathematical size restriction. No unbound variables
or extra geometric instances occur in the signature.

Independent searches, using different phrases from the first reader:

- `msearch.py K1 lem-weil-pbc-quasi-coherent-algebra-change-of-rings leanfinder
  "A tensor product over a quasi-coherent algebra of two quasi-coherent
  modules has affine sections computed by extension of scalars"`: eight
  hits, presheaf Monoidal.tensorObj and related maps plus ModuleCat.tilde;
  none states either sheaf change-of-rings conclusion.
- Loogle `SheafOfModules.IsQuasicoherent, ModuleCat.extendScalars`: zero hits.
- msearch grep `quasicoherent|Quasicoherent` in the sheaf ChangeOfRings
  module: zero hits. Direct rg in Mathlib's sheaf module sources confirms
  scalar restriction and quasi-coherence definitions, not this theorem.
- Direct rg in repository lean/Sheaf and source WeilConjectures for
  `changeOfRings|quasiCoherent_algebra_changeOfRings|quasicoherent.*tensor|
  quasi.*extendScalars`, and in dag/lean_names_upstream.json: only the
  recorded constructions and their derived/geometric users, plus
  AffineModuleCorrespondence's application in its special setup; no
  existing equivalent general theorem. No duplicate declaration found.

H5/H6/H8/H9: this module introduces no data definitions and proves nothing;
its sole theorem is `by sorry`. The source and blueprint identifier are in
both docstrings. The theorem docstring follows all seven node proof steps,
including the balancing quotient, inverse comparison maps and the actual
section-map comparison. The signature equals lean.statement verbatim.

Mismatches found: none. Changed only this report by adding the independent
second reading; retained the mathematical statement and Lean unchanged.

## Reviewer fix (R-qac1424)

The delivered statement encoded the algebras as bare ring sheaves `B C` with a separate
structure map `b : Y.sheaf ⟶ B` and C's structure map `b ≫ φ`, and wrote their
quasi-coherence by hand. Mathematically equivalent, but it is a second form of the shared
notion (STATE line QUASI-COHERENT O_X-ALGEBRAS; H4): restated with
`B C : Y.CommAlgebraSheaf` (`Under Y.sheaf`), `φ : B ⟶ C` (an O_Y-algebra map, so
`C.hom = B.hom ≫ φ.right`), `hB : B.toModule.IsQuasicoherent`,
`hC : C.toModule.IsQuasicoherent`, `P : SheafOfModules (𝓡 B.right)` with `hP` the
restriction along `B.hom`, change of rings `changeOfRings φ.right P`, the first conclusion
restricting along `C.hom`, and the sheafification unit over `𝓡 C.right`. Same clauses.
