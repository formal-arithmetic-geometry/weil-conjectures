import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elementary foundations" =>

This chapter will collect the elementary, Mathlib-adjacent toolkit of
Version I — everything that involves neither Frobenius modules nor
geometry:

* the formal $`\exp`/$`\log` calculus on $`\QQ`-algebras: mutually inverse
  group isomorphisms between $`(tR[\![t]\!], +)` and
  $`(1 + tR[\![t]\!], \times)`;
* $`t`-adically locally finite products and their logarithms (for the Euler
  product);
* the four-way equivalence for a power series: rational $`\iff` eventual
  linear recurrence $`\iff` finite-dimensional shift span $`\iff` finite
  Hankel rank;
* rank descent under field extension and the consequence
  $`K[\![t]\!] \cap L(t) = K(t)`;
* the integral Fatou lemma: $`f \in \ZZ[\![t]\!] \cap \QQ(t)` has a
  presentation $`A/B` with $`A, B \in \ZZ[t]` and $`B(0) = 1`, via the
  finitely generated shift lattice and Cayley–Hamilton over $`\ZZ`;
* the normalized Gauss lemma and uniqueness of reduced normalized
  fractions;
* field-theoretic leaves: the fixed field of
  $`\operatorname{Aut}(K/\QQ)` is $`\QQ`, and extension of complex
  embeddings under the cardinality bound $`\#K \leq 2^{\aleph_0}`.

Nodes will be added here as the corresponding Version-I milestones are
scheduled; several of the leaves (Cayley–Hamilton, Gauss's lemma, the
classification of algebraically closed fields) already exist in Mathlib and
will be recorded with the `mathlib` tag.
