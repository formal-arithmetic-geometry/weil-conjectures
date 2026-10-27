## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.FiniteWeilPairing` states
`AlgebraicGeometry.IsAbelianVariety.exists_finite_weilPairing`, with `sorry` as its only
proof. The three auxiliary declarations are real constructions or predicates belonging
to this same pairing notion; they are recorded in `lean.declarations`. No data are
chosen from an existence theorem. The original statement and proof are unchanged.
The statement dependencies additionally cite the already landed
`def-sfb-abelian-rational-duality-data`, which owns the bundled supplied duals used here.
There are no new DAG nodes and no dependency repairs.

Source read: Milne, *Abelian Varieties*, I §13, printed pp.57–58, including the displayed
construction `e_m(a,a') = g / (g ∘ t_a)`, Lemma 13.1, and Proposition 13.2(a),(d).
The node's nine proof steps are transcribed into the theorem docstring, including their
cited nodes. The normalized Poincare datum and polarization-calculus module were read
in full, as were the existing rational pairing and bundled-dual interfaces. The supplied
CompactObject example is now withdrawn and contains no declarations, so the live
DualPoincareDatum and PolarizationCalculus module headers supply the current convention.

Hypotheses and clauses:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`, with explicitly
  declared universe `u`. `ℓ : ℕ`, `[Fact ℓ.Prime]`, and `hℓ : ℓ ≠ ringChar k` render exactly
  the prime and characteristic condition. Characteristic zero is included.
- `A B : AbelianVarietyWithDual k` package arbitrary abelian varieties, their `GrpObj`
  structures and their supplied `AbelianDualPoincareDatum`. This uses the existing objects,
  and does not select a different dual or impose a polarization on either variety.
- `abelianFiniteTorsionPoints A m` abbreviates Mathlib's kernel of `powMonoidHom m` on
  `𝟙_ (Over (Spec (.of k))) ⟶ A`. This is exactly the subgroup `x ^ m = 1`, i.e. `m x = 0`
  in the node's additive notation. The notation is multiplicative because this is the
  existing group law on group-object points. Roots are the existing `rootsOfUnity m k`.
  The helper introduces no new torsion predicate or group law; it names an existing kernel.
- The existential `w` is simultaneous for every supplied dual datum and every positive
  level. The natural index `n` denotes level `n+1`; hence the first level is `ℓ`, and
  every node index `n ≥ 1` occurs. Nested `→*` give bilinearity, with multiplicative target.
- The first conjunct fixes the pairing to the canonical Poincare value. Its helper
  `abelianPoincarePointModule A y` is exactly `(1,y)^* P_A`. In
  `IsPoincareFiniteWeilValue`, `q = [m]` and `t_x` is the literal translation
  `lift (𝟙 A) (toUnit A ≫ x) ≫ μ[A]`. The equality `t_x ≫ q = q` records the torsion
  condition needed to type the deck identification. `Nonempty (q^* P_y ≅ O_A)` asserts
  triviality, and the following universal equation says for EVERY trivialization σ:
  `deck ≫ σ = t_x^* σ ≫ unitComparison ≫ multiplication(c)`.
  Here `deck` is exactly canonical `pullbackComp` followed by `pullbackCongr`, never an
  arbitrary isomorphism. Thus in Milne's rational-function expression the equality is
  `g = c (g ∘ t_x)`, so `c = g / (g ∘ t_x)`. The explicit nonemptiness prevents a vacuous
  universal condition. Scalar multiplication uses the structure morphism's map
  `k → Γ(A,O_A)`, followed by the existing `Scheme.Modules.smulHom`.
  Any trivialization differs by a global unit; on a proper geometrically integral abelian
  variety those are constants, so the ratio is unchanged. The predicate determines a
  unique scalar, because σ and the unit comparison are isomorphisms and scalar action is
  faithful, as can already be seen at the identity point. The Poincare source and its
  ratio convention are therefore part of the statement, rather than just docstring text.
- The second conjunct asserts `Finite` for both groups and `Function.Bijective (w A n)`
  and `Function.Bijective (w A n).flip`. Their codomains are precisely ALL group
  homomorphisms into `rootsOfUnity`; these are the two evaluation identifications.
- The third conjunct quantifies over points at `ℓ^(n+2)` and their lower-level values
  `x', y'`, whose underlying points are `x^ℓ, y^ℓ`. The conclusion is the equality of
  units `(w A (n+1) x y).val ^ ℓ = (w A n x' y').val`. Coercion to units allows comparison
  across the two root subgroups. This is the stated exponent ℓ, with ℓ multiplying BOTH
  inputs. No transition-lift choices are made: equality binders characterize the
  unique subtype elements. They always exist by the elementary power identity.
- In the fourth conjunct `a : A.variety ⟶ B.variety` has exactly `IsMonHom a`. The
  supplied `aDual` is characterized by the same Poincare-pullback isomorphism used in
  `exists_dual_polarization_calculus`: `(a × 1)^* P_B ≅ (1 × aDual)^* P_A`.
  That theorem gives its existence, uniqueness and homomorphism property. Hence the
  quantified maps are exactly the dual pullbacks of the node, with no additional
  assumption. `ax.val = x.val ≫ a` and `ay.val = y.val ≫ aDual` bind the images on torsion,
  and the conclusion is `w B n ax y = w A n x ay`. The images exist because those maps
  are homomorphisms. Using subtype values in this fashion avoids any postponed proof
  just to construct their membership certificates.
- The final conjunct quantifies over EVERY module `L` with `L.IsInvertible`, and EVERY
  `φ` satisfying the existing `ClassifiesAbelianDifference A.datum L φ`. The recorded
  polarization theorem characterizes exactly `φ_L` this way and proves it is a
  homomorphism. Subtype image values `φx`, `φy` are fixed by composition, and the
  conclusion is `w A n x φy = (w A n y φx)⁻¹`. There is no ampleness, isogeny, degree,
  oddness, or nontriviality assumption. Finite even-level alternation is not asserted.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed` (the algebraically closed clause of def-weil-algebraic-closure).
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`: `IsAbelianVariety`, with its
  proper/smooth/connected signature; `...AbelianVariety.Basic`: its commutativity instance.
- `Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`:
  `IsAbelianVariety.exists_dual_polarization_calculus`; its public dependency
  `...DualPoincareDatum`: `AbelianDualPoincareDatum`, `ClassifiesAbelianDifference`.
- `Sheaf.AlgebraicGeometry.AbelianVariety.RationalDualityData`:
  `AbelianVarietyWithDual`. The Poincare characterization in its `dualHomClassifies`
  agrees with the explicit unbundled morphism form here.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`; the Cartesian monoidal group API:
  rational-point group law; `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`; `Mathlib.AlgebraicGeometry.Modules.Sheaf`:
  `Scheme.Modules.pullback`, `pullbackComp`, `pullbackCongr`; the public module-dual
  dependency supplies `pullbackObjUnitIso`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`: `Scheme.Modules.smulHom`.
- `Mathlib.RingTheory.RootsOfUnity.Basic`: `rootsOfUnity`; the standard power homomorphism
  and kernel constructions; `Mathlib.Algebra.Group.Hom.Instances`: `MonoidHom.flip`.

Every recorded proof-dependency module is imported privately (the polarization and
abelian-basic modules are already public statement dependencies). In particular these
include EtaleFieldGsets, Descent, Isogeny, Torsion, RootsOfUnity.AlgebraicallyClosed,
Rigidity, AbelianSpacePoincareCalculus, and ModulePullbackTensor. The local source for
these recorded declarations was inspected. No downstream rational WeilPairing module is
imported: that theorem consumes this finite result, so importing it would close a cycle.

Edge cases checked: dimension zero gives trivial point groups and the unique perfect
pairing; the zero point gives scalar one by its identity translation. `ℓ = 2` is allowed
and only skew symmetry is stated. Characteristic zero remains allowed. Level `ℓ` is
present through index zero. The trivial line module and all nonample line modules remain
in scope. The identity, zero, arbitrary-degree and nonisogeny maps are allowed in the
functoriality clause. No point-lifting or nonzero-vector hypothesis excludes trivial
objects. All universes and binders are explicit; autoImplicit and relaxedAutoImplicit
are disabled. The source statement needs no correction and is not disputed.

Searches actually run, 2026-10-24:

- msearch leanfinder: “Canonical finite Weil pairing on prime to characteristic torsion of
  an abelian variety and its dual is perfect bilinear functorial and compatible with
  multiplication”: 8 hits, all root-system pairings, no finite geometric pairing.
- msearch leansearch: “The normalized Poincare line bundle defines a canonical perfect
  Weil pairing on finite torsion of an abelian variety and its dual”: 8 hits, abstract
  linear perfect-pairing results, no geometric construction.
- msearch loogle `"WeilPairing"`: 0 hits.
- msearch grep `WeilPairing|weilPairing|Poincare|biextension`: one Poincare recurrence
  mention in Dynamics/Ergodic/Conservative.lean, no matching notion.
- rg on project `WeilConjectures` and `Sheaf`: `WeilPairing|weilPairing|finiteWeil|AbelianDualPoincare|torsionPoints|Poincare`.
  Existing normalized dual data and the downstream rational pairing were found and read;
  no finite pairing. The other Weil/Poincare pairings concern cohomology.
- grep of this item id under `lean/WeilConjectures`: no match.
- rg `finite.?[Tt]orsion|PoincareFiniteWeilValue|abelianPoincarePointModule` in the project
  sources: no matching finite Weil-value construction or duplicate helper name.
- `tools/blueprint_refs.py search 'finite Weil pairing'`: 0 blueprint nodes;
  `ancestor lem-sfb-finite-torsion-weil-pairing` reports ancestor None, matching the node.
  DAG searches find this node and its rational-pairing consumer, not a second definition.

Validation: prescribed scompile.py confirmed the final module clean against current
server sources (9.7 s). The wrapper first reported a stale local-overlay timeout and
then automatically checked current sources: RationalHom 42.0 s, RationalDualityData 3.6 s,
our module 9.7 s. No timeout limit was changed. An earlier namespace error for smulHom
was repaired by naming `Scheme.Modules.smulHom` explicitly and importing its owning module.

Delivery validation: `deliver2.py Q98 lem-sfb-finite-torsion-weil-pairing --no-push`
printed `OK (dry run): commit 4686d303672 passes the preflight and compiles; nothing pushed`.
It compiled both the sandbox and actual library module names without additional warnings.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
