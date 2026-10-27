## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage states
AlgebraicGeometry.affineGroupHom_exists_faithfullyFlat_closedImmersion, with its entire
proof `sorry`. It introduces no definition, auxiliary theorem or new node. The node is
unchanged except for `lean`. Read Milne, Algebraic Groups (2017), printed pp.73–75,
Theorems 3.31 and 3.34 and Proposition 3.14 (printed p.68). Theorem 3.34 and its proof
say exactly the claimed affine homomorphism factorization. The docstring carries all
four accepted DAG proof steps, including the tensor-injectivity argument for the image
Hopf algebra and the one-chart closed-immersion criterion.

Hypotheses and conclusions, clause by clause:

- A field k: `{k : Type u} [Field k]`; u is explicitly declared. There is no assumption
  on characteristic, perfection or algebraic closure.
- G,H are k-schemes: `(G H : Over (Spec (.of k)))`; this includes their actual structure
  morphisms and makes every morphism below a morphism over the same field.
- Group scheme structures: `[GrpObj G] [GrpObj H]`, exactly the recorded dependency
  notion. No commutativity of the group law is assumed. The `IsMonHom` interface
  includes preservation of identity as well as multiplication, which is equivalent
  for group objects (as the node's proof explicitly observes).
- Affineness: `[IsAffine G.left] [IsAffine H.left]`.
- Finite type over k: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` and the
  corresponding two binders for H, exactly the conjunction in its definition node.
- A homomorphism f: `(f : G ⟶ H) [IsMonHom f]`.
- An affine group scheme I of finite type over k: the existential
  `(I : Over (Spec (.of k))) (_ : GrpObj I)` and the three conjuncts
  `IsAffine I.left`, `LocallyOfFiniteType I.hom`, `QuasiCompact I.hom`.
- Homomorphisms u and j: existential `(u : G ⟶ I) (j : I ⟶ H)` with the SAME
  existential group structure on I in `IsMonHom u ∧ IsMonHom j`.
- Factorization f = j composed with u: `u ≫ j = f`, using Lean's diagrammatic
  composition convention; reversing this equality does not change the clause.
- Closed immersion j: `IsClosedImmersion j.left`.
- k[X] is the actual global section ring: `Γ(I.left, ⊤)` and `Γ(G.left, ⊤)`.
  The final conjunct is `@Module.FaithfullyFlat Γ(I.left, ⊤) Γ(G.left, ⊤) _ _
  u.left.appTop.hom.toAlgebra.toModule`. Its module structure is explicitly the
  scalar restriction along u*, not an arbitrary or separately assumed action.
  Using the recorded module predicate directly also follows the project's
  faithfully-flat-module convention; no local instance or let binder is needed.
- No smoothness, reducedness, connectedness, perfectness or characteristic
  condition occurs. No additional clause occurs.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`, read its full declaration and docstring.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and scheme morphisms;
  Mathlib.AlgebraicGeometry.Group.Affine supplies the affine k-scheme and group-object
  API and `AlgebraicGeometry.hopfSpec` for the proof plan.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` (including its inherited
  MonObj structure and inverse identities); Mathlib.CategoryTheory.Monoidal.Mon:
  `CategoryTheory.IsMonHom`. Both are re-exported through Group.Affine. Read the
  recorded specialization explanation in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `AlgebraicGeometry.LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `AlgebraicGeometry.QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  `AlgebraicGeometry.IsClosedImmersion`, and the affine-cover criterion API.
- Mathlib.RingTheory.Flat.FaithfullyFlat.Basic: `Module.FaithfullyFlat` and its exactness
  characterization `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`. Also read
  Mathlib.RingTheory.RingHom.FaithfullyFlat: `RingHom.FaithfullyFlat`, whose definition
  is precisely this same module predicate with the action induced by the map.
- Proof-only import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra:
  `AlgebraicGeometry.affine_finiteType_algebra_of_field`, full signature/docstring read.
  The coordinate Hopf, spectrum-functor, affine-spectrum and closed-immersion-criterion
  proof dependencies have Mathlib matches, supplied by Group.Affine and ClosedImmersion.
  `lem-sfb-hopf-subalgebra-faithfully-flat` presently has neither Lean nor a Mathlib
  match, so no nonexistent proof module is imported; this is not a statement dependency.

Edge cases checked before writing: identity maps (I = G), trivial homomorphisms
(I = Spec k), closed subgroup inclusions (u an isomorphism), Frobenius on the additive
group in positive characteristic (faithfully flat but not smooth), and infinitesimal
nonreduced groups such as alpha_p. These impose none of the excluded conditions.
An empty underlying scheme cannot carry the required group identity over a field;
there is no additional nonemptiness binder. A single explicit universe u includes
arbitrary fields and schemes in that universe, and quantifies over no independent
smaller universe of test algebras.

Searches actually executed with msearch.py Q97 lem-sfb-affine-homomorphism-flat-image:

- leanfinder: "Every homomorphism of affine group schemes of finite type over a field
  factors as a faithfully flat homomorphism followed by a closed immersion". Eight
  hits, led by Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine and affine/closed
  immersion characterizations; no homomorphism factorization theorem.
- leansearch: "Every affine group scheme homomorphism of finite type over a field
  factors as a faithfully flat homomorphism and a closed immersion". Eight hits,
  likewise affine faithful flatness and closed-immersion criteria, no exact match.
- loogle: "IsMonHom, IsClosedImmersion, FaithfullyFlat". Unknown short identifier
  IsMonHom, not evidence of absence. Repeated with fully qualified query
  "AlgebraicGeometry.IsClosedImmersion, RingHom.FaithfullyFlat": zero hits.
- grep: "faithfullyFlat|faithfully_flat|flat_image" in AlgebraicGeometry/Group: zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for the item id, faithful-flatness and
  factorization names: the proper-source image theorem in GroupScheme/Image.lean
  assumes properness and lacks faithful flatness; Sheaf's HomomorphismFactorization
  states a more general separated-group quotient theorem with extra conclusions,
  not this exact statement. Existing rational-point and quotient lemmas reference
  the item only in proof docstrings. No duplicate of the new declaration was found.

Validation: scompile.py compiled both its sandbox probe and the library module on
2026-10-24, clean with no errors or warnings (3.2 s / 6.0 s). All writes are confined
to the assigned sandbox; no direct Git command or global build was used.

No statement dispute, statement correction or dependency interface fault was found.

## Second reading by Q97

Reopened the item and the delivered signature after compilation and checked the
field, the two affine finite-type group structures, and multiplication-compatible
f against their binders. Checked that the existential I is a group over the same
Spec k, with affineness and both finite-type clauses, and that u and j use that
very group structure. Checked the order of composition, the closed immersion on
j's underlying scheme map, and faithful flatness with the module action induced
by u's actual global-section map. No hypothesis or conclusion mismatch was found,
and no change was needed. The nilpotent and positive-characteristic cases remain
included. This is the worker's own final rereading; the dispatcher's independent
maintainer review remains separate, and no other agent was started.
