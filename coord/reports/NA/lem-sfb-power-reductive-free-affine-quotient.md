## Worker report

The module `Sheaf.AlgebraicGeometry.PowerReductiveFreeAffineQuotient` states
`AlgebraicGeometry.power_reductive_free_affine_quotient`, with its only theorem proof
`sorry`. Three helpers give the actual orbit coequalizer, its fppf sheafification and
the canonical projection followed by the sheafification unit. They contain real data,
and are listed in `lean.declarations`. They belong to the quotient notion in this item;
there is no additional independent definition node or dependency repair.

The item statement and every field except `lean` are preserved.

Source read: Alper, *Adequate moduli spaces and geometrically reductive group schemes*,
Proposition 9.7.8 (printed p.528), Lemma 9.2.5(3), Theorem 4.3.1, journal PDF
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf. Proposition 9.7.8 applies to
principal homogeneous spaces and does not impose finite type on X. The node's five-step
proof, including the torsor descent argument for finite presentation, is transcribed
into the theorem docstring with all named inputs.

Hypotheses and clauses, in order:

| Node | Lean rendering |
| --- | --- |
| R commutative, S = Spec R | `R : CommRingCat.{u}`; every base is `Spec R`. |
| S-group scheme with all group diagrams | `G : Scheme.{u}`, `[G.Over (Spec R)]`, `[GrpObj (G.asOver (Spec R))]`. Mathlib's internal group object includes associative multiplication, unit and inverse. |
| G affine over S | `[IsAffine G]`. Since S is affine, this is equivalent to `IsAffineHom (G ↘ Spec R)` by Mathlib's affine-morphism criterion; it is used to obtain the canonical coordinate Hopf structure. |
| G flat | `[Flat (G ↘ Spec R)]`. |
| G finitely presented in the node's convention | `[LocallyOfFinitePresentation (G ↘ Spec R)]`, `[QuasiCompact (G ↘ Spec R)]`, `[QuasiSeparated (G ↘ Spec R)]`, explicitly all three. |
| Every base-changed R-algebra R' | First binders of `hpower`: `(R' : Type u) [CommRing R'] [Algebra R R']`. |
| Arbitrary commutative R'-algebras E and F | `(E F : Type u) [CommRing E] [CommRing F] [Algebra R' E] [Algebra R' F]`; there are no finiteness or nontriviality assumptions. |
| Actions by algebra coactions | `ρE : E →ₐ[R'] E ⊗[R'] (R' ⊗[R] Γ(G, ⊤))` and `ρF` of the analogous type. The second tensor factor is canonically the coordinate algebra of G after base change. |
| Counitality for both coactions | The two equations using `TensorProduct.rid`, `Coalgebra.counit.lTensor`, and `LinearMap.id`. |
| Coassociativity for both coactions | The two equations using `TensorProduct.assoc`, `ρ.toLinearMap.rTensor`, and `Coalgebra.comul.lTensor`. |
| Surjective equivariant algebra map | `f : E →ₐ[R'] F`, `Function.Surjective f`, and the equality `f.toLinearMap.rTensor … ∘ₗ ρE.toLinearMap = ρF.toLinearMap ∘ₗ f.toLinearMap`. |
| Invariant b and a positive power with invariant lift | `∀ b : F, ρF b = b ⊗ₜ[R'] 1 → ∃ (N : ℕ) (e : E), 1 ≤ N ∧ ρE e = e ⊗ₜ[R'] 1 ∧ f e = b ^ N`. |
| Affine S-scheme X | `X : Over (Spec R)` and `[IsAffine X.left]`. |
| Right G-action | The scheme morphism `a : X ⊗ G.asOver (Spec R) ⟶ X`, with `hunit` saying x·1=x and `hmul` saying (x·g)·h=x·(g*h), on every test S-scheme. Naturality is inherent in a scheme morphism. |
| Free on every test scheme | `hfree`: for all T, x and g, `lift x g ≫ a = x → g = 1`. This includes non-affine and nonreduced tests. |
| Fppf sheafification of right orbits | `affineRightOrbitPresheaf` is the presheaf coequalizer of `yoneda.map (fst X G)` and `yoneda.map a`. `affineRightQuotient` applies `presheafToSheaf` to its universe lift. The coequalizer is sectionwise orbits because `hunit` and `hmul` are group-action laws. |
| Y algebraic space, and q the actual quotient arrow | `Y : AlgebraicSpace (Spec R)`, `q : yoneda.obj X ⟶ Y.obj.obj`, `equot` identifying its lifted presheaf with the sheaf quotient, and `hq` identifying the lifted q with the orbit projection followed by sheafification and this isomorphism. Thus q is not an arbitrary unrelated map. |
| Fppf local sections | `hsections`: for every y over every test T there is a covering sieve K in the big fppf topology, and over each arrow b in K a section x lifting the restriction of y. |
| Canonical torsor isomorphism | `htorsor : IsPullback (yoneda.map (fst X G)) (yoneda.map a) q q`. It says precisely that (x,g) ↦ (x,xg) identifies X×_S G with X×_Y X, with its specified projections. Products here are slice products, hence scheme fibre products over S. |
| Y represented by an affine S-scheme | Existential `U : Over (Spec R)`, `IsAffine U.left`, and `e : yoneda.obj U ≅ Y.obj.obj`. Representability of a sheaf is equivalently representability of its underlying presheaf. Since Spec R and U are affine, U→Spec R is affine as well. |
| q affine and finitely presented | Existential `f : X ⟶ U` with `yoneda.map f ≫ e.hom = q` and `IsAffineHom f.left ∧ LocallyOfFinitePresentation f.left ∧ QuasiCompact f.left ∧ QuasiSeparated f.left`. All three finite-presentation clauses are present. |
| No finite-type condition on X→S | None occurs in any binder. |

Universe check: the base ring, schemes, test algebras and algebraic-space sections all
use u. No independently smaller test-algebra universe is introduced. All R'-algebras
in the working universe are covered. Concrete sheafification on the big site uses
`Type (u+1)`; the quotient comparison uses the canonical `uliftFunctor.{u+1,u}` on both
the quotient source and Y, including `hq`. This is a faithful change of value universe,
not an extra representability or smallness assumption. Every universe and binder is
explicit, with `set_option autoImplicit false`.

Dependency declarations used, read with signatures and docstrings:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`; the cartesian Hom
  group is `CategoryTheory.Hom.group` in `Monoidal.Cartesian.Grp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom` and
  `isAffine_of_isAffineHom`, with the converse affine-source/affine-target instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`; the big relative
  site is `Scheme.fppfTopology.over (Spec R)`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  the full subcategory of fppf sheaves with representable diagonal and an etale
  surjective scheme atlas. No substitute algebraic-space notion is used.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`: `TensorProduct`,
  `TensorProduct.lift`, `LinearMap.rTensor`; tensor associator and right unitor are
  the standard tensor transports. The canonical coordinate Hopf algebra comes from
  `Mathlib.AlgebraicGeometry.Group.Affine`, and scalar extension from
  `Mathlib.RingTheory.HopfAlgebra.TensorProduct`.

Existing proof dependency modules are imported without `public`:
`AlgebraicSpaceFppfCoveringCalculus`, `AlgebraicSpaceFourPropertyFppfDescent`,
`AlgebraicStackQuasicompactSurjection`, and the Mathlib scheme affine-morphism,
separatedness, coproduct and affine fibre-product inputs. The three proof prerequisites
`lem-sfb-representable-flat-lfp-fppf-descent`, `lem-sfb-affine-torsor-algebra-invariants`,
`lem-sfb-space-power-lifting-affineness` currently have no recorded modules to import.
They are only proof dependencies, so this does not prevent stating the item.

Searches for an existing statement or exact reusable notion:

- `msearch.py leanfinder`, “A free action of a geometrically reductive affine group
  scheme on an affine scheme has affine fppf quotient”: eight hits, affine-space
  instances and ordinary affine morphism facts, no quotient theorem.
- `msearch.py loogle`, `AlgebraicGeometry.IsAffineHom, CategoryTheory.GrpObj`: no hits.
- `msearch.py grep`, `coaction|power_reductive|geometricallyReductive` in
  `AlgebraicGeometry`: no hits.
- `msearch.py leansearch`, “Universal power lifting of invariant elements along
  equivariant surjections of commutative algebras”: eight hits, surjective-algebra-map
  lifts and universe lifts, no invariant lifting statement.
- `msearch.py leanfinder`, “Universal invariant power lifting for algebra coactions
  of an affine group scheme over a commutative ring”: eight affine-space hits, no match.
- `msearch.py loogle`, `Bialgebra.counitAlgHom, Bialgebra.comulAlgHom`: six hits about
  bialgebra maps and Hopf structure constructors, no invariant power-lifting predicate.
- `msearch.py grep`, `structure.*Coaction|UniversalInvariantPower|PowerReductive`: no hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and proposed names:
  no existing statement. Concept searches found `HopfAction.AlgebraCoaction` in
  `Sheaf.RingTheory.HopfActionModuleData`, but its base is restricted to a field.
  We therefore use the ordinary algebra-map and coalgebra equations directly,
  with no duplicated coaction definition and no field hypothesis.
- Concept searches also found `groupSpaceOrbitPresheaf`, `groupSpaceQuotient` and
  `groupSpaceQuotientMap` in `FreeFlatGroupSpaceQuotient`. They take a left action
  in sheaves over a base algebraic-space sheaf. Our helpers directly apply the same
  Mathlib coequalizer and sheafification to the specified right scheme action;
  they introduce no alternative quotient predicate or abstract arbitrary map.
- `tools/blueprint_refs.py search 'universal invariant power'`: zero blueprint matches.
  DAG definition-statement searches found no universal ring-base invariant power-lifting
  definition. `blueprint_refs.py ancestor` reports ancestor None for this supporting item.

Edge cases checked before finalizing: the zero ring and empty base are allowed; X can
be empty; E or F can be the zero algebra; N=0 is excluded by `1 ≤ N`, and N=1 is allowed;
no characteristic, smoothness, Noetherianity, connectedness or finite-generation restriction
occurs. For the trivial group this reduces to the expected affine quotient of affine X.
For a trivial action of a nontrivial group on nonempty X, `hfree` fails on test points,
so the theorem cannot silently apply. Covering sieves allow the empty covering of an
empty test scheme. The explicit coaction equations retain nilpotent information.

Validation: `scompile.py NA lem-sfb-power-reductive-free-affine-quotient <module>` compiled
both sandbox and library module cleanly (5.7 and 5.8 seconds). The initial attempt used
only affine structure-morphism data; the coordinate Hopf API needs an `IsAffine G`
instance, so the equivalent affine-object hypothesis replaced it. This is an equivalent
rendering over affine Spec R, not a statement correction. No node fault or
STATEMENT-DISPUTED issue remains.

## Second reading by NA

This dispatcher assignment forbids other agents and assigns independent delivery review
to the maintainer. This section records the worker's final audit, not a claim that a
second person reviewed it. Reading the node beside the final signature confirms the
table above clause by clause. In particular, arbitrary base algebras and arbitrary
equivariant algebra surjections are retained; both counit and both coassociativity
equations are present; the right-action multiplication order is (xg)h=x(gh); freeness
uses all test schemes; `hq` pins q to the actual sheaf quotient; `htorsor` fixes the
two projections; and the conclusion includes the representing arrow and all finite-
presentation conditions. No extra finite-type hypothesis, chosen noncanonical map,
or unconnected existence datum is substituted. The source and definition checks found
no further mismatch. The affine-object adjustment needed for the coordinate Hopf API
is explained above.
