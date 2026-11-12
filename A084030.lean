import A084029

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # A084030 — corollaire d'A084029

Texte OEIS verbatim : « Main diagonal of triangle A084029. »
Commentaire : « Conjecture: Only one term is zero. »
Données : 1,0,120,2020,10400,100140,1001203,…
(a(2) = 0 : la ligne 2 de A084029 est [20,0].)

Le corollaire voisin A084033 (quotients T(n,k)/n) vit dans
`A084033.lean`, qui importe ce fichier.

Fidélité de l'énoncé validée à l'aveugle par argon
(A084030/VERIFICATIONS/A084030-resp.txt, verdict VRAI) :
« n ≤ (witnesses n).card » = « la ligne n est pleine (pas de
zero-padding) ». -/

namespace A084030

/-- Ensemble fini des témoins de la ligne n de A084029 : les
    multiples de n à n chiffres dont les chiffres somment à n.
    Tout N à n chiffres vérifie N < 10^n donc appartient au range
    — `witnesses n` contient la ligne complète. -/
def witnesses (n : ℕ) : Finset ℕ :=
  (Finset.range (10 ^ n)).filter fun N =>
    n ∣ N ∧ (Nat.digits 10 N).length = n ∧ (Nat.digits 10 N).sum = n

theorem mem_witnesses {n N : ℕ}
    (h : n ∣ N ∧ (Nat.digits 10 N).length = n
      ∧ (Nat.digits 10 N).sum = n) :
    N ∈ witnesses n :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
    have hlt := Nat.lt_base_pow_length_digits (b := 10) (m := N)
      (by norm_num)
    rwa [h.2.1] at hlt), h⟩

/-- La ligne n ≥ 3 est pleine : le Finset de ≥ n témoins fourni
    par A084029 s'inclut dans `witnesses n`. -/
theorem card_witnesses_ge (n : ℕ) (hn : 3 ≤ n) :
    n ≤ (witnesses n).card := by
  obtain ⟨s, hs, hv⟩ := _root_.A084029 n hn
  exact hs.trans (Finset.card_le_card fun N hN =>
    mem_witnesses (hv N hN))

end A084030

open A084030 in
/-- A084030 — « Only one term is zero » : pour n ≥ 3 la ligne n de
    A084029 est pleine, donc le terme diagonal a(n) existe et est
    non nul. -/
theorem A084030 (n : ℕ) (hn : 3 ≤ n) : n ≤ (witnesses n).card :=
  card_witnesses_ge n hn

open A084030 in
/-- Unicité du zéro : a(2) = 0 — seul 20 est témoin de la ligne 2. -/
theorem A084030_zero_unique : (witnesses 2).card = 1 := by
  decide

open A084030 in
/-- Ligne 1 pleine : a(1) = 1 (le seul témoin est 1). -/
theorem A084030_one : (witnesses 1).card = 1 := by
  decide

#print axioms A084030
#print axioms A084030_zero_unique
#print axioms A084030_one
