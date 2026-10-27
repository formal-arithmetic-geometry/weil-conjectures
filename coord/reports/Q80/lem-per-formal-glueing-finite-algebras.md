## Worker report

The module `Sheaf.RingTheory.FormalGlueingFiniteAlgebras` states
`FormalGlueing.exists_finite_algebra_of_formalGlueing`, with its single proof
postponed by `sorry`. No definitions, helper theorems, or dependency repairs
are needed. The input node and its proof are unchanged outside `lean`.
The source is Stacks Project, More on Algebra, Tags 05ER and 05EU; the local
source at `literature/stacks-project/more-algebra.tex`, especially the final
three sentences of `remark-formal-glueing-algebras`, was read.

Hypotheses and clauses:

- Commutative rings R and S are `[CommRing R] [CommRing S]`. An arbitrary
  homomorphism φ is represented by `[Algebra R S]` and `algebraMap R S`:
  any specified φ supplies this instance via `φ.toAlgebra`. No injectivity
  or surjectivity is added.
- Flatness is `hflat : (algebraMap R S).Flat`, precisely the recorded
  `RingHom.Flat` predicate.
- The nonnegative integer t and its t elements are `(t : ℕ)` and
  `(f : Fin t → R)`. K is `Ideal.span (Set.range f)`.
- The induced quotient map is the actual `Ideal.quotientMap` to the
  quotient by `K.map (algebraMap R S)`, and `hquot` asserts its bijectivity.
  For a ring homomorphism, this is exactly being a ring isomorphism.
- The commutative S-algebra E' is `(E' : Type w) [CommRing E']
  [Algebra S E']`. Its R-algebra structure and `[IsScalarTower R S E']`
  specify restriction along φ, rather than an independent base map.
- The commutative R_fi-algebras are `(E : Fin t → Type w)` with the
  displayed commutative-ring and `Algebra (Localization.Away (f i))`
  instances. The R-algebra instances and scalar towers specify their
  restrictions along the canonical localization maps. Every such input
  algebra supplies these instances, so these are structure bookkeeping.
- `α i : E' ⊗[R] R_fi ≃ₐ[S] S ⊗[R] E i` represents the specified
  prime-chart algebra isomorphism. These are the algebra-localization
  tensor models; tensor symmetry switches the source's E_i ⊗ S order.
  Specifying an S-algebra isomorphism here is equivalent to specifying an
  S_fi-algebra isomorphism: fi already acts invertibly on both sides,
  and an S-linear map necessarily commutes with the inverse of its action.
- `αij i j : E i ⊗[R] R_fj ≃ₐ[R] E j ⊗[R] R_fi` represents the
  chart-chart isomorphism. Both fi and fj act invertibly on both sides;
  the R-algebra map thus automatically respects R_(fi*fj). No linearity
  or base-algebra compatibility in the source is discarded.
- `hdatum` asserts existence of the recorded `FormalGlueing.Data` object
  with precisely these underlying component modules, by equalities of
  `ModuleCat` objects. The HEq fields identify its transitions on all
  numerator generators with the specified algebra transitions. For the
  overlap target, `LocalizedModule.equivTensorProduct` and
  `TensorProduct.comm` identify the recorded module-localization model
  with the tensor model of algebra localization. This is a comparison
  using Mathlib, not a second definition of a gluing datum.
  Agreement on numerators determines each full transition: every
  localized element is a numerator divided by a power and both maps are
  linear with respect to that invertible element. The recorded `Data`
  supplies the square and cocycle equations, with its actual canonical
  comparison and interchange maps. Conversely the node's compatible
  algebra datum supplies exactly this `hdatum`; it is not a stronger
  separate descent assumption.
- `hfinite' : Module.Finite S E'` is finite generation of the prime
  component as a module, and `hfinite` is finite generation of every
  chart over its own R_fi. These are not finiteness as sets or merely
  finite type as algebras.
- The existential `(D : Type (max u v w)) (_ : CommRing D)
  (_ : Algebra R D)` gives the required commutative R-algebra;
  `Module.Finite R D` asserts the required finite generation.
- `q' : S ⊗[R] D ≃ₐ[S] E'` is the required base-change algebra
  isomorphism (again using tensor symmetry), and
  `q i : R_fi ⊗[R] D ≃ₐ[R_fi] E i` is the required localization
  algebra isomorphism, in its standard tensor model.
- The first final conjunct is the prime-chart square evaluated on d/1:
  α_i(q'(1⊗d)⊗1) = 1⊗q_i(1⊗d). Multiplying by S-scalars and inverse
  powers of fi gives that square on every fraction of a pure tensor;
  additivity then gives it on the whole module.
- The second final conjunct is the chart-chart square on d/1/1:
  α_ij(q_i(1⊗d)⊗1) = q_j(1⊗d)⊗1. Multiplying by inverse powers of
  fi and fj gives the square on every double fraction. Thus these
  equations say the component algebra isomorphisms are an isomorphism
  of canonical and specified gluing data. The inverse component maps
  satisfy the reverse squares by composing with the bijective forward
  maps; an additional inverse-compatibility assumption is unnecessary.

The common component universe w is arbitrary, and the output universe is
`max u v w`. Any finite family of input algebra carriers fits a common
universe, raising by ULift if necessary; no bound below the base-ring
universes is imposed on test objects. The source theorem is invariant
under these canonical changes of carriers. All variables and universes
are bound explicitly, and `autoImplicit false` is set in the module.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`.
- `WeilConjectures.RingTheory.FormalGlueingData`: `FormalGlueing.Data`,
  `restrict`, `piece`, `localize`, `compare`, `swap`, and its category
  interface. Its full structure, the square/cocycle signatures and the
  `Hom` compatibility equations were read.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct` and
  `LinearMap.baseChange` (reexported through FormalGlueingData).
- `Mathlib.Algebra.Module.LocalizedModule.Basic`:
  `LocalizedModule.Away` and `LocalizedModule.mkLinearMap`; inherited
  through FormalGlueingData. `LocalizedModule.mk` is numerator insertion.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`,
  inherited through FormalGlueingData. Algebra structure is Mathlib's
  localization structure, not an alternative construction.
- `Mathlib.RingTheory.Localization.BaseChange`:
  `LocalizedModule.equivTensorProduct`; its signature and numerator
  formula `equivTensorProduct_apply_mk` were read.

Plain imports preserve the proof plan:
`WeilConjectures.RingTheory.FormalGlueingEquivalence`
(`FormalGlueing.exists_canonical_equivalence`),
`WeilConjectures.RingTheory.FormalGlueingComplexExact`
(`RingTheory.formalGlueingComplexExact`),
`WeilConjectures.RingTheory.FormalGlueingH0` (`FormalGlueing.h0`), and
`Sheaf.RingTheory.FiniteIffFormalGlueing`
(`Module.finite_iff_formalGlueing`). Their recorded declarations,
signatures and relevant docstrings were read. No import cycle is added.

Edge cases checked before writing:

- t = 0: the chart maps, compatibility and finiteness are empty families.
  K = 0 and the quotient hypothesis makes φ an isomorphism; the theorem
  reduces to transport of a finite S-algebra to R. `Fin 0` is permitted.
- fi = 0 or fi nilpotent: its localization is the zero ring. Unital
  algebras over it are zero rings; tensor localization and module
  localization agree and the formulas still make sense.
- fi a unit, including fi = 1: its chart is over R and is unchanged by
  localization; the compatibility clauses retain their full meaning.
- Zero base rings and zero E' or E_i: there is no `Nontrivial` assumption.
  Commutative unital zero algebras are admitted, and finite generation
  of the zero module is included.
- Repeated generators and diagonal overlaps i = j are not excluded.
  `Data` retains its square and cocycle equations also in these cases.
- u, v, w are independent. Enlarging the output to their maximum permits
  all module/tensor/localization carriers occurring in a gluing proof.

Searches for an existing theorem (all via prescribed msearch.py):

1. leanfinder: "Formal gluing finite commutative algebras along a flat
   ring homomorphism and finitely many principal localizations".
   Eight hits: finite-presentation and finite-type localization criteria,
   including `Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway`
   and `Algebra.FiniteType.of_span_eq_top_source`; none is this algebra
   existence theorem for a formal gluing datum.
2. loogle: `"Algebra", "Glue"`. Twelve ringed-space GlueData hits;
   none states this ring-theoretic formal algebra gluing theorem.
3. grep in Mathlib/RingTheory:
   `formalGlue|formal_glu|[Gg]lueing|patching`: zero hits.
4. leansearch: "Gluing finite commutative algebras along a flat map
   isomorphic modulo a finitely generated ideal". Eight hits: flatness,
   Picard tensor products and scheme gluing; no matching theorem.
5. rg over `lean/WeilConjectures` and `lean/Sheaf` for formal glueing,
   gluing and finite-algebra names finds the recorded module framework,
   but no algebraization theorem for finite commutative algebra data.
   The exact blueprint id and proposed declaration name have no hit
   in either source tree; `dag/lean_names_upstream.json` also has no
   occurrence of the proposed declaration.

Validation: the final module (with `autoImplicit false`) passed both
scompile.py modes on the server, in 7.5 s and 1.8 s. The prescribed
`deliver2.py Q80 lem-per-formal-glueing-finite-algebras --no-push`
returned `OK (dry run)`: commit ecd566f1051 passes preflight and compiles.
Only the module, the item's lean record and this report are delivered.
No statement correction, new node, STATEMENT-DISPUTED flag or
dependency-record fault is needed.

## Second reading by Q80

A second in-thread reading compared the node with the final module after
compilation. Per the dispatcher's explicit instruction, no other agent
was started; this section does not claim an independent-agent review.
The maintainer's independent review remains the delivery review.

The reread checked each item above: arbitrary φ as algebraMap, flatness,
K and the actual induced quotient homomorphism, arbitrary finite chart
family, the two kinds of commutative base algebras, the precise module
datum, both finite-generation hypotheses, finite commutative output,
the two kinds of algebra isomorphisms, and both compatibility squares.
The point requiring care was the scalar action on a chart viewed as an
R-module: the recorded `piece` uses restriction of scalars, whereas the
input algebra carries its R-algebra action. The scalar tower identifies
these actions, but the initial full-linear-map composition required
definitional equality during elaboration. The final statement instead
uses HEq of numerator functions, with Mathlib's tensor-localization
comparison on the overlap target. This retains precisely the same
specified transition maps, because localization maps are determined by
their numerator values. The server then accepted the complete signature.

The concluding generator equations were also checked against the
node's full commuting-square requirement: S-linearity and inverted
powers extend the first square, and the two inverted chart elements
extend the second. Thus neither square is weakened to a condition that
holds only on an insufficient family of elements. No further mismatch
was found and no natural-language node field was changed.
