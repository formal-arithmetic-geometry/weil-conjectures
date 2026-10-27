## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianAlgebraicEquivalenceNorm` states
`AlgebraicGeometry.Scheme.Modules.semiabelian_algebraic_equivalence_norm`, with
one `sorry` and no definitions. It states the supplied node, without a statement
correction, over an arbitrary field. The original Raynaud volume is WANTED in
the source record: its general semiabelian formulation is explicitly an agent
prerequisite, not represented here as a verbatim theorem of Raynaud. I read the
node's six-step proof, the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`,
and the available Milne AV I Proposition 8.4 and Remark 8.5 (printed pp.35–36,
PDF pp.41–42), which give the multiplicativity/inversion calculation in the
abelian case. The theorem docstring reproduces all six proof steps and their
prerequisite ids. This delivery states the generalization requested by the node.

Hypotheses and clauses:

- The arbitrary field is `{k : Type u} [Field k]`; there is no perfectness,
  algebraic-closedness, separability, or characteristic assumption on k.
- The actual k-group scheme is `H : Grp (Over (Spec (.of k)))`. Its group
  operations and group identities are the bundled `GrpObj` operations;
  `[IsCommMonObj H.X]` is commutativity. Its inverse morphism over k is
  `ι[H.X]`; `.left` is its underlying scheme map.
- Smoothness and separatedness are `[Smooth H.X.hom]` and
  `[IsSeparated H.X.hom]`. The latter is Mathlib's diagonal closed-immersion
  definition. Finite type is `[LocallyOfFiniteType H.X.hom]` together with
  `[QuasiCompact H.X.hom]`, exactly the recorded finite-type convention.
- `_hsemi` existentially supplies the rank `r : ℕ`, the quotient group `A`,
  and group morphisms `i` and `q`, all over `AlgebraicClosure k`.
  `MultiplicativeType.baseChange` equips the actual fibre product with its
  pulled-back group law. `MultiplicativeType.splitTorus` is the existing
  product of Spec(kbar[t,t^-1]), with the terminal group for r=0.
- `IsAbelianVariety A.X` says proper, smooth, connected. Over the algebraically
  closed field used here, connectedness is geometric connectedness. This is
  exactly the node's proper smooth geometrically connected quotient group;
  it adds neither a polarization nor an ample line nor a dimension constraint.
- `IsPullback i.hom.hom (toUnit ...) q.hom.hom η[A.X]` identifies the entire
  scheme-theoretic kernel, with its actual group inclusion. Together with
  `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over ...) (yoneda.map
  q.hom.hom)`, it gives the exact sequence of fppf sheaves. This is the same
  encoding as the landed SemiabelianGeometricFibres module, specialized to
  the one algebraic closure explicitly named by this node. There is no split
  extension or torus-splitting assumption over k.
- `P T : H.X.left.Modules`, `[P.IsInvertible]`, and `[T.IsInvertible]` are the
  two invertible modules on H, with the upstream scheme-level predicate.
- `_hT` applies the existing `AreAlgebraicallyEquivalent` to the tensor
  pullback of T and the structure module on the actual base-changed H.
  `pullback.fst H.X.hom (Spec.map ... (algebraMap k (AlgebraicClosure k)))`
  is the projection H_kbar -> H, and the over-scheme in the relation is
  `((MultiplicativeType.baseChange ...).obj H).X`. These carriers agree by
  the definitions. The recorded relation is the reflexive symmetric
  transitive closure of isomorphisms and pairs of fibres of one invertible
  module on H_kbar times a smooth connected separated finite-type parameter
  variety. Its fibre maps use rational points over the algebraically closed
  field. Thus it is precisely geometric algebraic triviality as defined in
  the item, including a chain of families rather than one family only.
- Clause (i) is `Nonempty ((tensorPullback (ι[H.X]).left).obj T ≅ dual T)`.
  `dual T` is the upstream internal Hom to the structure module.
- The stated consequence in (i) is the separate conjunct
  `Nonempty (T ⊗ (tensorPullback (ι[H.X]).left).obj T ≅ 𝟙_ H.X.left.Modules)`.
- Clause (ii) is `IsAmple H.X.left (P ⊗ T) ↔ IsAmple H.X.left P`, using the
  absolute scheme-level ampleness predicate. In particular, this is NOT the
  projective-over-a-field predicate also named AlgebraicGeometry.IsAmple.
  All three conclusions are on H itself, over k.

Dependency declarations used (their signatures and docstrings were read):

- `Field` in Mathlib.Algebra.Field.Defs; `Scheme` and its morphisms in
  Mathlib.AlgebraicGeometry.Scheme.
- `Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `LocallyOfFiniteType` and `QuasiCompact` in the recorded Mathlib morphism
  modules; `IsProper`/`IsSeparated` in the recorded proper/separated modules.
- `Scheme.Modules.IsInvertible` in
  WeilConjectures.AlgebraicGeometry.Modules.Invertible;
  `Scheme.Modules.dual` in WeilConjectures.AlgebraicGeometry.Modules.Dual.
- `Scheme.Modules.IsAmple` in WeilConjectures.AlgebraicGeometry.Ample.
- `Scheme.Modules.tensorPullback` is the explicit upstream tensor
  construction, exported through the recorded
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction. Its normalized
  adjunction is not needed in the signature; there is no copied pullback.
- The tensor is the existing sheaf tensor; the recorded module
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses is public
  imported. Scheme module tensor and unit are the upstream monoidal ones.
- `AlgebraicClosure` in Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure;
  the scheme base change is the existing pullback used by
  WeilConjectures.AlgebraicGeometry.BaseChangeConventions and by
  MultiplicativeType.baseChange.
- `Scheme.fppfTopology` in Mathlib.AlgebraicGeometry.Sites.Fpqc, its over-site
  in Mathlib.CategoryTheory.Sites.Over, and local surjectivity in
  Mathlib.CategoryTheory.Sites.LocallySurjective.
- `Grp`, `GrpObj`, `IsCommMonObj`, inverse, identity and group morphisms are
  the recorded Mathlib.CategoryTheory.Monoidal.Grp notions.
- `MultiplicativeType.baseChange` and `MultiplicativeType.splitTorus` in
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType;
  `Scheme.Modules.AreAlgebraicallyEquivalent` and its generating step in
  Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence;
  `IsAbelianVariety` in WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs.
  Their three already-landed definition nodes are added to stmt_deps; no
  new node or dependency repair is needed.

The available recorded proof dependency modules are imported without `public`:
CubicalRigidifiedLine, AmplePullback, Modules.VeryAmple,
RelativeAmpleAbsoluteTwist, AffineInvertibleFiniteSetSection,
AffineCapSectionOpen, AmplePositiveTensorPower, Morphisms.Etale and
Morphisms.FiberDegree. The proof prerequisites with no Lean declaration yet
are semiabelian-picard-multiplicative-torsor, space-relative-ampleness-fpqc-descent,
semiabelian-cubical-rigidification, semiabelian-invertible-multiplication and
finite-locally-free-ample-reflection (all with the lem-sfb- prefix). They are
proof dependencies only, and are not required to type this statement. Caution
for stage 3: the recorded `lem-sc-ample-tensor` declaration in VeryAmple uses
the projective-over-a-field notion; the absolute tensor argument on nonproper
semiabelian schemes must use the absolute criterion, without adding properness.

Edge cases checked before writing: r=0 (abelian variety); quotient dimension zero
(tori); the trivial group and zero-dimensional quotient; T equal to the structure
module; P arbitrary, including nonample; inversion in characteristic two;
imperfect k; a nonsplit torus over k. All remain allowed. The empty scheme cannot
carry the given group identity over a field. A single explicit universe u allows
arbitrary fields and schemes at that size, and their algebraic closure has the
same universe; no independent smaller parameter universe makes the equivalence
relation vacuous. No formal proof of any edge case was added.

Searches actually run:

- msearch.py leanfinder: "Inversion pullback of algebraically trivial line bundles
  on a semiabelian variety is dual and twisting preserves ampleness". Eight hits,
  including CommRing.Pic.inv_eq_dual and convex AmpleSet lemmas; none is this
  scheme-theoretic semiabelian statement.
- msearch.py loogle: `"IsAmple", "AreAlgebraicallyEquivalent"`: zero hits.
- msearch.py grep: `semiabelian|[Aa]lgebraically[Tt]rivial` in AlgebraicGeometry:
  zero Mathlib hits.
- msearch.py leansearch: "For a semiabelian variety inversion pulls an
  algebraically trivial invertible sheaf back to its dual and twisting preserves
  ampleness". Eight hits on ring Picard groups and functoriality of inverse maps
  or module pullback; none states the result.
- rg on lean/WeilConjectures for semiabelian, AreAlgebraicallyEquivalent and
  algebraicallyTrivial, and the exact item id: no matching statement. rg on
  lean/Sheaf found LineAlgebraicEquivalence, ToriMultiplicativeType,
  SemiabelianGeometricFibres, and GeometricSemiabelianSplitQuotient, whose full
  relevant declarations were read. Related abelian-space multiplicativity is
  for proper families, not the present semiabelian field-level conclusion.
- DAG searches for those declaration names located the existing definition
  nodes. No duplicate statement or missing independent notion was found.

No STATEMENT-DISPUTED issue or correction is asserted. The missing original
Raynaud source and the absolute-versus-projective proof interface distinction
above remain documented limitations for the later proof, not additional
hypotheses or changes to the statement.

Validation: prescribed scompile.py compiled the sandbox module and its final
library-path form cleanly (13.8 s and 1.8 s); no errors or warnings were printed.

## Second reading by Q05

This is a self re-reading, not a claim of an independent worker review: the
assignment prohibits spawning another agent; the maintainer independently reads
the delivery. I reopened the node and final module and checked every binder and
conjunct against the mapping above. In particular I checked that the geometric
extension is existential only over the chosen algebraic closure, that the kernel
square uses the actual quotient and identity, that the line is trivial in the
family-generated relation after tensor pullback, and that both isomorphisms and
the ampleness biconditional are over the original field. I checked the source
of AreAlgebraicallyEquivalent: smooth, connected, separated finite-type parameters
are exactly the smooth connected varieties of the source convention. The
quotient's IsAbelianVariety is equivalent to the supplied proper smooth geometric
connectedness condition over kbar. No hypothesis, characteristic case, direction
of the biconditional, or norm clause is absent. No correction was needed after
this reading. Only lean and the three added landed stmt_deps change in the item.
