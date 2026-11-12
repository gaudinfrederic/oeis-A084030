import Mathlib
import A077754
import A084029Table
import Scratch029_cert_lo
import Scratch029_cert_hi1
import Scratch029_cert_hi2a
import Scratch029_cert_hi2b
import Scratch029_cert_hi2c
import Scratch029_cert_hi2d

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # A084029 — conjecture de Murthy (2003)

Pour tout n ≥ 3, il existe au moins n multiples de n à
exactement n chiffres décimaux dont la somme des chiffres
vaut n (le seul zéro du triangle OEIS A084029 est en ligne 2 :
pour n = 2, seul 20 convient).

Énoncé validé à l'aveugle par argon
(A084029/VERIFICATIONS/A084029-stmt-resp.txt).

Architecture de la preuve :
- n ≤ 130 : table `table029` de n témoins explicites
  (certificat `decide` kernel, cas par cas).
- n ≥ 131 : construction à deux blocs. On écrit
  n = 2^a·5^b·m avec gcd(m,10) = 1, z = max a b,
  LA = max(3(m/27+1)+4, (z+8)/4), J = n - LA, T = J - z,
  s_B = n - 5·LA, F = T - s_B = 4·LA - z, G = F - 3,
  p = (s_B + 2)/3.
  Pour chaque triplet (x,y,w) dans
  [G, G+p) × [G+p, G+2p) × [G+2p, G+3p), on pose
  O = {0..G-1} ∪ {x,y,w} (F positions de zéros),
  I = {0..T-1} ∖ O (s_B positions de 1), B = ofDigits(0^z ∥ 1_I)
  de sorte que 10^z | B et σ(B) = s_B, puis on résout la fibre
  A par `residue_reach` au résidu -B·10^{-J} — la condition de
  coset mod g = gcd(9,m) est automatique car B ≡ σ(B) mod 9 et
  g | m | n donc 5·LA ≡ -s_B mod g — et on obtient
  N = B + 10^J·A avec n | N, σ(N) = s_B + 5LA = n, et
  J + LA = n chiffres.
  (x,y,w) ↦ N est injectif : N mod 10^J = B détermine la
  liste indicatrice, donc I, donc O, donc {x,y,w} dont les
  trois intervalles disjoints donnent x, y, w. Le cardinal est
  p³ ≥ n. -/

namespace A084029

/-- Liste indicatrice : 1 exactement aux positions de I. -/
def indList (T : ℕ) (I : Finset ℕ) : List ℕ :=
  (List.range T).map fun k => if k ∈ I then (1 : ℕ) else 0

theorem indList_length (T : ℕ) (I : Finset ℕ) :
    (indList T I).length = T := by
  simp [indList]

theorem indList_getElem? {T : ℕ} (I : Finset ℕ) {k : ℕ}
    (hk : k < T) :
    (indList T I)[k]? = some (if k ∈ I then 1 else 0) := by
  simp only [indList, List.getElem?_map, List.getElem?_range hk,
    Option.map_some]

/-- La somme de l'indicatrice compte les positions filtrées. -/
private theorem map_ind_sum (I : Finset ℕ) (l : List ℕ) :
    (l.map fun k => if k ∈ I then (1 : ℕ) else 0).sum
      = (l.filter (· ∈ I)).length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.filter, ih]
      by_cases h : a ∈ I
      · simp [h]
        omega
      · simp [h]

/-- La somme de l'indicatrice vaut card I (I ⊆ range T). -/
theorem indList_sum {T : ℕ} {I : Finset ℕ}
    (hI : I ⊆ Finset.range T) :
    (indList T I).sum = I.card := by
  rw [indList, map_ind_sum]
  have hnd : ((List.range T).filter (· ∈ I)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter,
      List.toFinset_range]
  simp only [decide_eq_true_eq]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hI]

/-- Injectivité de l'indicatrice sur les parties de range T. -/
theorem indList_inj {T : ℕ} {I₁ I₂ : Finset ℕ}
    (h1 : I₁ ⊆ Finset.range T) (h2 : I₂ ⊆ Finset.range T)
    (h : indList T I₁ = indList T I₂) : I₁ = I₂ := by
  ext k
  by_cases hk : k < T
  · have e : (indList T I₁)[k]? = (indList T I₂)[k]? :=
      congrArg (fun l => l[k]?) h
    rw [indList_getElem? I₁ hk, indList_getElem? I₂ hk] at e
    simp only [Option.some.injEq] at e
    by_cases h1k : k ∈ I₁ <;> by_cases h2k : k ∈ I₂ <;>
      simp_all
  · constructor <;> intro hkm
    · exact absurd (Finset.mem_range.mp (h1 hkm)) hk
    · exact absurd (Finset.mem_range.mp (h2 hkm)) hk

/-- Le bloc bas B : z zéros suivis de la liste indicatrice. -/
def witLo (z T : ℕ) (I : Finset ℕ) : ℕ :=
  Nat.ofDigits 10 (List.replicate z 0 ++ indList T I)

/-- Valeur du bloc bas : B = 10^z · ofDigits(ind). -/
theorem witLo_val (z T : ℕ) (I : Finset ℕ) :
    witLo z T I = 10 ^ z * Nat.ofDigits 10 (indList T I) := by
  show Nat.ofDigits 10 (List.replicate z 0 ++ indList T I) = _
  rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero,
      List.length_replicate]
  ring

/-- Chiffres de B (quand I contient T-1 : dernier = 1). -/
theorem witLo_digits {z T : ℕ} {I : Finset ℕ}
    (hT : T - 1 ∈ I) (hI : I ⊆ Finset.range T) :
    Nat.digits 10 (witLo z T I)
      = List.replicate z 0 ++ indList T I := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_append, List.mem_replicate] at hd
    rcases hd with ⟨-, rfl⟩ | hd
    · norm_num
    · simp only [indList, List.mem_map] at hd
      obtain ⟨k, -, rfl⟩ := hd
      by_cases h : k ∈ I <;> simp [h]
  · intro hne
    have hT0 : T ≠ 0 := by
      rintro rfl
      simpa using hI hT
    have hin : indList T I ≠ [] := by
      simp [indList, hT0]
    simp only [List.getLast_append_of_ne_nil _ hin]
    simp [indList, hT]

theorem witLo_sigma {z T s : ℕ} {I : Finset ℕ}
    (hT : T - 1 ∈ I) (hI : I ⊆ Finset.range T)
    (hs : I.card = s) :
    (Nat.digits 10 (witLo z T I)).sum = s := by
  rw [witLo_digits hT hI, List.sum_append, indList_sum hI, hs]
  simp

/-- Le témoin complet : bloc bas ++ liste de la fibre. -/
def witN (z T LA : ℕ) (I : Finset ℕ) (u : ℕ → ℕ) : ℕ :=
  Nat.ofDigits 10 ((List.replicate z 0 ++ indList T I)
    ++ (List.range LA).map fun e => 1 + u e)

/-- Valeur : witN = witLo + 10^J · fibre. -/
theorem witN_val {z T LA J : ℕ} (I : Finset ℕ) (u : ℕ → ℕ)
    (hJ : z + T = J) :
    witN z T LA I u
      = witLo z T I + 10 ^ J * fibre u LA := by
  show Nat.ofDigits 10 ((List.replicate z 0 ++ indList T I)
        ++ (List.range LA).map fun e => 1 + u e)
      = Nat.ofDigits 10 (List.replicate z 0 ++ indList T I)
        + 10 ^ J
          * Nat.ofDigits 10 ((List.range LA).map fun e => 1 + u e)
  rw [Nat.ofDigits_append, List.length_append,
      List.length_replicate, indList_length, hJ]

/-- Chiffres de witN. -/
theorem witN_digits {z T LA : ℕ} {I : Finset ℕ} {u : ℕ → ℕ}
    (hu : ∀ e < LA, u e ≤ 8) (hI : I ⊆ Finset.range T)
    (hT : T - 1 ∈ I) :
    Nat.digits 10 (witN z T LA I u)
      = (List.replicate z 0 ++ indList T I)
        ++ (List.range LA).map fun e => 1 + u e := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro d hd
    rw [List.mem_append] at hd
    rcases hd with hd | hd
    · rw [List.mem_append, List.mem_replicate] at hd
      rcases hd with ⟨-, rfl⟩ | hd
      · norm_num
      · simp only [indList, List.mem_map] at hd
        obtain ⟨k, -, rfl⟩ := hd
        by_cases h : k ∈ I <;> simp [h]
    · rw [List.mem_map] at hd
      obtain ⟨e, he, rfl⟩ := hd
      have := hu e (List.mem_range.mp he)
      omega
  · intro hne
    have hT0 : T ≠ 0 := by
      rintro rfl
      simpa using hI hT
    have hin : indList T I ≠ [] := by
      simp [indList, hT0]
    by_cases hLA : LA = 0
    · subst hLA
      simp only [List.range_zero, List.map_nil, List.append_nil]
      simp only [List.getLast_append_of_ne_nil _ hin]
      simp [indList, hT]
    · have hLAne : ((List.range LA).map fun e => 1 + u e) ≠ [] := by
        simp [hLA]
      simp only [List.getLast_append_of_ne_nil _ hLAne,
        List.getLast_map, List.getLast_range]
      have := hu (LA - 1) (by omega)
      omega

/-- Solveur de fibre empaqueté : pour tout bloc bas B de somme
    s_B avec s_B + 5·LA = n et g = gcd(9,m) | n, il existe u
    (u_e ≤ 8, Σu = 4·LA) tel que B + 10^J · fibre u LA ≡ 0 [m].
    C'est le contenu du bloc coset de `existence_Rm`,
    reparamétré (L+K ↦ 5·LA+0). -/
theorem reach_fibre {m : ℕ} (hm : Nat.Coprime m 10) {LA J : ℕ}
    (hLA : 3 * (m / 27 + 1) + 4 ≤ LA) {n B s_B : ℕ}
    (hg : Nat.gcd 9 m ∣ n) (hBsig : (Nat.digits 10 B).sum = s_B)
    (hsum : s_B + 5 * LA = n) :
    ∃ u : ℕ → ℕ, (∀ e < LA, u e ≤ 8) ∧
      ((List.range LA).map u).sum = 4 * LA ∧
      ((fibre u LA : ZMod m) * (10 : ZMod m) ^ J
        + (B : ZMod m) = 0) := by
  haveI : NeZero m := ⟨by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; norm_num at hm
    · exact Nat.ne_of_gt h⟩
  have hunit : IsUnit ((10 : ZMod m) ^ J) :=
    IsUnit.pow _ ((ZMod.isUnit_iff_coprime 10 m).mpr
      (Nat.coprime_comm.mp hm))
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  set t : ZMod m := -(B : ZMod m) * v with ht
  have htgt : t * (10 : ZMod m) ^ J + (B : ZMod m) = 0 := by
    rw [ht, mul_assoc]
    have hv' : (v : ZMod m) * (10 : ZMod m) ^ J = 1 := by
      rw [mul_comm]; exact hv
    rw [hv']; simp
  -- condition de coset : t = ↑(5·LA+0) + g·c (mod m)
  have hcos : ∃ c : ℤ, t = ((5 * LA + 0 : ℕ) : ZMod m) +
      ((Nat.gcd 9 m : ℕ) : ZMod m) * (c : ZMod m) := by
    have hg9 : Nat.gcd 9 m ∣ 9 := Nat.gcd_dvd_left 9 m
    have hgm : Nat.gcd 9 m ∣ m := Nat.gcd_dvd_right 9 m
    set g := Nat.gcd 9 m
    haveI : NeZero g := ⟨Nat.ne_of_gt
      (Nat.gcd_pos_of_pos_left m (by norm_num))⟩
    have hmodg : B ≡ s_B [MOD g] := by
      have h9 : (9 : ℤ) ∣ (s_B : ℤ) - B := by
        rw [← hBsig]
        exact Nat.ModEq.dvd (Nat.modEq_nine_digits_sum B)
      have hg9z : (g : ℤ) ∣ 9 := Int.natCast_dvd_natCast.mpr hg9
      exact Nat.modEq_of_dvd (dvd_trans hg9z h9)
    have hcast : ZMod.castHom hgm (ZMod g) t =
        ((5 * LA + 0 : ℕ) : ZMod g) := by
      have hcv : ZMod.castHom hgm (ZMod g) v = 1 := by
        have hmul := congrArg (ZMod.castHom hgm (ZMod g)) hv
        rw [map_mul, map_one] at hmul
        have h10d : ZMod.castHom hgm (ZMod g)
            ((10 : ZMod m) ^ J) = 1 := by
          rw [map_pow]
          have h10g : ((10 : ℕ) : ZMod g) = 1 := by
            rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
            exact (Nat.modEq_zero_iff_dvd.mpr hg9).add
              (Nat.ModEq.refl 1)
          rw [show (10 : ZMod m) = ((10 : ℕ) : ZMod m) from rfl,
              map_natCast, h10g, one_pow]
        rw [h10d, one_mul] at hmul
        exact hmul
      have hBg : ((B : ℕ) : ZMod g) = ((s_B : ℕ) : ZMod g) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact hmodg
      have hLKg : ((5 * LA + 0 : ℕ) : ZMod g) =
          -((s_B : ℕ) : ZMod g) := by
        have hsum' : 5 * LA + 0 + s_B = n := by omega
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, hsum']
        exact (CharP.cast_eq_zero_iff (ZMod g) g n).mpr hg
      rw [ht, map_mul, map_neg, map_natCast, hcv, mul_one, hBg, hLKg]
    -- (t - ↑(5LA+0)).val divisible par g -> le coset c
    set w := t - ((5 * LA + 0 : ℕ) : ZMod m)
    have hz : ZMod.castHom hgm (ZMod g) w = 0 := by
      rw [map_sub, hcast, map_natCast, sub_self]
    have hcv2 : ZMod.castHom hgm (ZMod g) w =
        ((w.val : ℕ) : ZMod g) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val w]
      rw [map_natCast]
    rw [hcv2] at hz
    have hdv : g ∣ w.val :=
      (CharP.cast_eq_zero_iff (ZMod g) g w.val).mp hz
    refine ⟨((w.val / g : ℕ) : ℤ), ?_⟩
    have ht2 : t = ((5 * LA + 0 : ℕ) : ZMod m) + w :=
      (add_sub_cancel _ _).symm
    rw [ht2]; congr 1
    rw [Int.cast_natCast, ← Nat.cast_mul,
        Nat.mul_div_cancel' hdv, ZMod.natCast_zmod_val]
  obtain ⟨u, hu8, huK, hut⟩ :=
    residue_reach m hm t LA 0 hLA (by norm_num) hcos
  refine ⟨u, hu8, ?_, ?_⟩
  · simpa using huK
  · rw [hut]; exact htgt

/-- L'ensemble O des positions de zéros du bloc bas :
    les G premières positions plus {x, y, w}. -/
def Oset (G : ℕ) (t : (ℕ × ℕ) × ℕ) : Finset ℕ :=
  Finset.range G ∪ ({t.1.1, t.1.2, t.2} : Finset ℕ)

/-- L'ensemble I des positions de 1 du bloc bas. -/
def Iset (T G : ℕ) (t : (ℕ × ℕ) × ℕ) : Finset ℕ :=
  Finset.range T \ Oset G t

/-- Le bloc bas B(t). -/
def Bf (z T G : ℕ) (t : (ℕ × ℕ) × ℕ) : ℕ :=
  witLo z T (Iset T G t)

/-- Le théorème pour n ≥ 131 : construction à deux blocs et
    famille cubique de triplets de positions de zéros. -/
theorem A084029_large (n : ℕ) (hn : 131 ≤ n) :
    ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s,
      n ∣ N ∧ (Nat.digits 10 N).length = n
        ∧ (Nat.digits 10 N).sum = n := by
  have hn0 : n ≠ 0 := by omega
  -- factorisation n = R·m, R = 2^a·5^b, gcd(m,10) = 1
  set q1 := Nat.divMaxPow n 2 with hq1
  set a := padicValNat 2 n with ha
  have hq1n : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn0
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hq1n; exact hn0 hq1n.symm
  set m := Nat.divMaxPow q1 5 with hm
  set b := padicValNat 5 q1 with hb
  have hmq : m * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have h5m : ¬ 5 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have hmq1 : m ∣ q1 := ⟨5 ^ b, hmq.symm⟩
  have hq1n' : q1 ∣ n := ⟨2 ^ a, hq1n.symm⟩
  have h2m : ¬ 2 ∣ m := fun h => h2q1 (h.trans hmq1)
  have hmc2 : Nat.Coprime m 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr h2m).symm
  have hmc5 : Nat.Coprime m 5 :=
    (Nat.prime_five.coprime_iff_not_dvd.mpr h5m).symm
  have hmc10 : Nat.Coprime m 10 := by
    have hc := Nat.Coprime.mul_right hmc2 hmc5
    rwa [show (2 : ℕ) * 5 = 10 from rfl] at hc
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hmc10; norm_num at hmc10
    · exact h
  haveI : NeZero m := ⟨hmpos.ne'⟩
  set z := max a b with hzdef
  set R := 2 ^ a * 5 ^ b with hRdef
  have hnm : n = R * m := by rw [← hq1n, ← hmq]; ring
  have hmn : m ∣ n := ⟨R, by rw [hnm, mul_comm]⟩
  have hmle : m ≤ n := Nat.le_of_dvd (by omega) hmn
  have hRc : Nat.Coprime R m :=
    (Nat.Coprime.mul_right (Nat.Coprime.pow_right a hmc2)
      (Nat.Coprime.pow_right b hmc5)).symm
  have hR10 : R ∣ 10 ^ z := by
    have h25 : Nat.Coprime (2 ^ a) (5 ^ b) :=
      Nat.Coprime.pow_left a
        (Nat.Coprime.pow_right b (by norm_num : Nat.Coprime 2 5))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h25
      ((pow_dvd_pow_of_dvd (by norm_num : (2 : ℕ) ∣ 10) a).trans
        (pow_dvd_pow 10 (le_max_left a b)))
      ((pow_dvd_pow_of_dvd (by norm_num : (5 : ℕ) ∣ 10) b).trans
        (pow_dvd_pow 10 (le_max_right a b)))
  have h2zn : 2 ^ z ≤ n := by
    have h2an : 2 ^ a ≤ n :=
      Nat.le_of_dvd (by omega)
        (pow_padicValNat_dvd (p := 2) (n := n))
    have h2bn : 2 ^ b ≤ n := by
      have h5b : 5 ^ b ≤ n := Nat.le_of_dvd (by omega)
        ((pow_padicValNat_dvd (p := 5) (n := q1)).trans hq1n')
      exact le_trans (Nat.pow_le_pow_left (by norm_num) b) h5b
    rcases le_total a b with h | h
    · rw [max_eq_right h] at hzdef
      rw [hzdef]; exact h2bn
    · rw [max_eq_left h] at hzdef
      rw [hzdef]; exact h2an
  have hz16 : z ≤ n / 16 := by
    by_cases h7 : z ≤ 8
    · have h8 : 8 ≤ n / 16 := by omega
      omega
    · push_neg at h7
      have h16z : 16 * z ≤ 2 ^ z := by
        have hge : z - 7 ≤ 2 ^ (z - 8) := by
          have h : z - 8 < 2 ^ (z - 8) := Nat.lt_two_pow_self
          omega
        calc 16 * z ≤ 256 * (z - 7) := by omega
          _ = 2 ^ 8 * (z - 7) := by norm_num
          _ ≤ 2 ^ 8 * 2 ^ (z - 8) :=
              Nat.mul_le_mul (le_refl _) hge
          _ = 2 ^ z := by rw [← pow_add]; congr 1; omega
      have hz' : z ≤ 2 ^ z / 16 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc z * 16 = 16 * z := by ring
          _ ≤ 2 ^ z := h16z
      exact le_trans hz' (Nat.div_le_div_right h2zn)
  -- paramètres de la construction
  set LA := max (3 * (m / 27 + 1) + 4) ((z + 8) / 4) with hLAdef
  set J := n - LA with hJdef
  set T := J - z with hTdef
  set s_B := n - 5 * LA with hsBdef
  set F := T - s_B with hFdef
  set G := F - 3 with hGdef
  set p := (s_B + 2) / 3 with hpdef
  -- faits arithmétiques
  have hLAge1 : 3 * (m / 27 + 1) + 4 ≤ LA := le_max_left _ _
  have hLAge2 : (z + 8) / 4 ≤ LA := le_max_right _ _
  have hLAle : LA ≤ n / 9 + 7 := by
    apply max_le
    · have hd : m / 27 ≤ n / 27 := Nat.div_le_div_right hmle
      have h39 : 3 * (n / 27) ≤ n / 9 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc 3 * (n / 27) * 9 = (n / 27) * 27 := by ring
          _ ≤ n := Nat.div_mul_le_self n 27
      omega
    · apply le_trans (Nat.div_le_div_right
        (show z + 8 ≤ n / 16 + 8 by omega))
      rw [Nat.div_le_iff_le_mul_add_pred (by norm_num)]
      omega
  have hLA5 : 5 * LA ≤ n - 3 := by omega
  have hLAn : LA ≤ n := by omega
  have hsBn : s_B + 5 * LA = n := by omega
  have hzJ : z ≤ J := by omega
  have hzT : z + T = J := by omega
  have hJn : J + LA = n := by omega
  have hsBT : s_B ≤ T := by omega
  have hTeq : T = F + s_B := by omega
  have hTge : 1 ≤ T := by omega
  have h9sB : 4 * n ≤ 9 * s_B + 315 := by omega
  have hFge : 5 ≤ F := by omega
  have hG3p : G + 3 * p ≤ T - 1 := by omega
  have h3p : s_B ≤ 3 * p := by omega
  have h4n : 4 * n ≤ 27 * p + 315 := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    push_neg at h
    omega
  have hcub : 27 * p + 315 ≤ 4 * p * p * p := by
    have h25 : 25 ≤ p * p := Nat.mul_le_mul hp5 hp5
    have h5 : p * 100 ≤ p * (4 * (p * p)) := by
      apply Nat.mul_le_mul_left
      omega
    calc 27 * p + 315 ≤ 100 * p := by omega
      _ = p * 100 := by ring
      _ ≤ p * (4 * (p * p)) := h5
      _ = 4 * p * p * p := by ring
  have hpn : n ≤ p * (p * p) := by
    have h4 : 4 * n ≤ 4 * (p * (p * p)) := by
      calc 4 * n ≤ 27 * p + 315 := h4n
        _ ≤ 4 * p * p * p := hcub
        _ = 4 * (p * (p * p)) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  -- la famille d'indices
  set X := Finset.Ico G (G + p) with hXdef
  set Y := Finset.Ico (G + p) (G + 2 * p) with hYdef
  set W := Finset.Ico (G + 2 * p) (G + 3 * p) with hWdef
  set fam := (X ×ˢ Y) ×ˢ W with hfamdef
  -- bornes d'un triplet
  have hbnd : ∀ x y w, (⟨⟨x, y⟩, w⟩ : (ℕ × ℕ) × ℕ) ∈ fam →
      G ≤ x ∧ x < G + p ∧ G + p ≤ y ∧ y < G + 2 * p ∧
      G + 2 * p ≤ w ∧ w < G + 3 * p := by
    intro x y w ht
    rw [hfamdef] at ht
    simp only [Finset.mem_product] at ht
    obtain ⟨⟨hx, hy⟩, hw⟩ := ht
    rw [hXdef] at hx
    rw [hYdef] at hy
    rw [hWdef] at hw
    obtain ⟨hx1, hx2⟩ := Finset.mem_Ico.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_Ico.mp hy
    obtain ⟨hw1, hw2⟩ := Finset.mem_Ico.mp hw
    exact ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩
  have hOcard : ∀ t ∈ fam, (Oset G t).card = F := by
    rintro ⟨⟨x, y⟩, w⟩ ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hdj : Disjoint (Finset.range G)
        ({x, y, w} : Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro e he hmem'
      rw [Finset.mem_range] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
      rcases hmem' with rfl | rfl | rfl <;> omega
    have h3 : ({x, y, w} : Finset ℕ).card = 3 := by
      have hxy : x ≠ y := by omega
      have hxw : x ≠ w := by omega
      have hyw : y ≠ w := by omega
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxw]),
        Finset.card_insert_of_notMem (by simp [hyw]),
        Finset.card_singleton]
    have hO : Oset G (⟨x, y⟩, w) = Finset.range G ∪ {x, y, w} := rfl
    rw [hO, Finset.card_union_of_disjoint hdj, h3,
      Finset.card_range]
    omega
  have hOsub : ∀ t ∈ fam, Oset G t ⊆ Finset.range T := by
    rintro ⟨⟨x, y⟩, w⟩ ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hO : Oset G (⟨x, y⟩, w) = Finset.range G ∪ {x, y, w} := rfl
    rw [hO]
    apply Finset.union_subset
    · intro e he
      rw [Finset.mem_range] at he ⊢
      omega
    · intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;>
        rw [Finset.mem_range] <;> omega
  have hIcard : ∀ t ∈ fam, (Iset T G t).card = s_B := by
    intro t ht
    have : Iset T G t = Finset.range T \ Oset G t := rfl
    rw [this, Finset.card_sdiff_of_subset (hOsub t ht),
      Finset.card_range, hOcard t ht]
    omega
  have hTmem : ∀ t ∈ fam, T - 1 ∈ Iset T G t := by
    rintro ⟨⟨x, y⟩, w⟩ ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hI : Iset T G (⟨x, y⟩, w)
        = Finset.range T \ Oset G (⟨x, y⟩, w) := rfl
    rw [hI, Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_range]; omega
    · intro hO
      have hO' : T - 1 ∈ Finset.range G ∪ ({x, y, w} : Finset ℕ) :=
        hO
      rw [Finset.mem_union] at hO'
      rcases hO' with hO' | hO'
      · rw [Finset.mem_range] at hO'
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hO'
        rcases hO' with h | h | h <;> omega
  have hIsub : ∀ t ∈ fam, Iset T G t ⊆ Finset.range T := by
    intro t ht
    have : Iset T G t = Finset.range T \ Oset G t := rfl
    rw [this]; exact Finset.sdiff_subset
  have hOinv : ∀ t ∈ fam,
      Finset.range T \ Iset T G t = Oset G t := by
    intro t ht
    have : Iset T G t = Finset.range T \ Oset G t := rfl
    rw [this]
    exact Finset.sdiff_sdiff_eq_self (hOsub t ht)
  have htri : ∀ x y w, (⟨⟨x, y⟩, w⟩ : (ℕ × ℕ) × ℕ) ∈ fam →
      Oset G ((x, y), w) \ Finset.range G
        = ({x, y, w} : Finset ℕ) := by
    intro x y w ht
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ ht
    have hO : Oset G ((x, y), w) \ Finset.range G
        = (Finset.range G ∪ {x, y, w}) \ Finset.range G := rfl
    rw [hO]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
      not_lt]
    constructor
    · rintro ⟨hmem'', hge⟩
      rcases hmem'' with hlt | he | he | he
      · omega
      · subst he; exact Or.inl rfl
      · subst he; exact Or.inr (Or.inl rfl)
      · subst he; exact Or.inr (Or.inr rfl)
    · rintro (he | he | he)
      · subst he
        exact ⟨Or.inr (Or.inl rfl), by omega⟩
      · subst he
        exact ⟨Or.inr (Or.inr (Or.inl rfl)), by omega⟩
      · subst he
        exact ⟨Or.inr (Or.inr (Or.inr rfl)), by omega⟩
  have hBsig : ∀ t ∈ fam, (Nat.digits 10 (Bf z T G t)).sum
      = s_B := by
    intro t ht
    exact witLo_sigma (hTmem t ht) (hIsub t ht) (hIcard t ht)
  have hBdigits : ∀ t ∈ fam, Nat.digits 10 (Bf z T G t)
      = List.replicate z 0 ++ indList T (Iset T G t) := by
    intro t ht
    exact witLo_digits (hTmem t ht) (hIsub t ht)
  have hBlt : ∀ t ∈ fam, Bf z T G t < 10 ^ J := by
    intro t ht
    calc Bf z T G t < 10 ^ (Nat.digits 10 (Bf z T G t)).length :=
          Nat.lt_base_pow_length_digits (by norm_num)
      _ = 10 ^ J := by
          rw [hBdigits t ht, List.length_append,
            List.length_replicate, indList_length, hzT]
  -- le solveur de fibre par triplet (total, pour pouvoir faire
  -- un choix global ; la conclusion résiduelle n'est garantie
  -- que pour t ∈ fam)
  have hmem : ∀ t ∈ fam, ∃ u : ℕ → ℕ,
      (∀ e < LA, u e ≤ 8) ∧
      ((List.range LA).map u).sum = 4 * LA ∧
      ((fibre u LA : ZMod m) * (10 : ZMod m) ^ J
        + (Bf z T G t : ZMod m) = 0) := by
    intro t ht
    exact reach_fibre hmc10 hLAge1
      (dvd_trans (Nat.gcd_dvd_right 9 m) hmn) (hBsig t ht) hsBn
  have hmemT : ∀ t : (ℕ × ℕ) × ℕ, ∃ u : ℕ → ℕ,
      (∀ e < LA, u e ≤ 8) ∧
      ((List.range LA).map u).sum = 4 * LA ∧
      (t ∈ fam → (fibre u LA : ZMod m) * (10 : ZMod m) ^ J
        + (Bf z T G t : ZMod m) = 0) := by
    intro t
    by_cases ht : t ∈ fam
    · obtain ⟨u, h1, h2, h3⟩ := hmem t ht
      exact ⟨u, h1, h2, fun _ => h3⟩
    · refine ⟨fun _ => 4, fun e he => ?_, ?_, fun h => absurd h ht⟩
      · exact Nat.le_of_lt (by norm_num)
      · simp only [List.map_const', List.sum_replicate,
          List.length_range, smul_eq_mul]
        omega
  set uf : (ℕ × ℕ) × ℕ → ℕ → ℕ :=
    fun t => Classical.choose (hmemT t) with hufdef
  have huf8 : ∀ t, ∀ e < LA, uf t e ≤ 8 :=
    fun t => (Classical.choose_spec (hmemT t)).1
  have hufK : ∀ t, ((List.range LA).map (uf t)).sum = 4 * LA :=
    fun t => (Classical.choose_spec (hmemT t)).2.1
  have hufres : ∀ t ∈ fam, (fibre (uf t) LA : ZMod m)
      * (10 : ZMod m) ^ J + (Bf z T G t : ZMod m) = 0 :=
    fun t ht => (Classical.choose_spec (hmemT t)).2.2 ht
  -- l'ensemble des témoins
  set s := fam.image (fun t => witN z T LA (Iset T G t) (uf t))
      with hsdef
  -- les témoins sont deux à deux distincts
  have hmodB : ∀ t ∈ fam,
      witN z T LA (Iset T G t) (uf t) % 10 ^ J = Bf z T G t := by
    intro t ht
    rw [witN_val (Iset T G t) (uf t) hzT, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hBlt t ht)
  have hinj : Set.InjOn
      (fun t => witN z T LA (Iset T G t) (uf t)) fam := by
    rintro t₁ h1 t₂ h2 heq
    have h1' : t₁ ∈ fam := Finset.mem_coe.mp h1
    have h2' : t₂ ∈ fam := Finset.mem_coe.mp h2
    have heq' : witN z T LA (Iset T G t₁) (uf t₁)
        = witN z T LA (Iset T G t₂) (uf t₂) := heq
    -- B₁ = B₂ via mod 10^J
    have hB12 : Bf z T G t₁ = Bf z T G t₂ := by
      have e1 := hmodB t₁ h1'
      have e2 := hmodB t₂ h2'
      rw [← e1, heq', e2]
    -- indList injective -> I₁ = I₂
    have hI12 : Iset T G t₁ = Iset T G t₂ := by
      apply indList_inj (hIsub t₁ h1') (hIsub t₂ h2')
      have hd : Nat.digits 10 (Bf z T G t₁)
          = Nat.digits 10 (Bf z T G t₂) := by rw [hB12]
      rw [hBdigits t₁ h1', hBdigits t₂ h2'] at hd
      exact (List.append_right_inj _).mp hd
    -- O₁ = O₂ par involution du sdiff
    have hO12 : Oset G t₁ = Oset G t₂ := by
      rw [← hOinv t₁ h1', ← hOinv t₂ h2', hI12]
    -- {x,y,w}₁ = {x,y,w}₂
    rcases t₁ with ⟨⟨x₁, y₁⟩, w₁⟩
    rcases t₂ with ⟨⟨x₂, y₂⟩, w₂⟩
    obtain ⟨hx1, hx2, hy1, hy2, hw1, hw2⟩ := hbnd _ _ _ h1'
    obtain ⟨kx1, kx2, ky1, ky2, kw1, kw2⟩ := hbnd _ _ _ h2'
    have hset : ({x₁, y₁, w₁} : Finset ℕ)
        = {x₂, y₂, w₂} := by
      have e1 := htri _ _ _ h1'
      have e2 := htri _ _ _ h2'
      rw [hO12] at e1
      rw [e1] at e2
      exact e2
    -- x₁ = x₂ : seul élément du premier intervalle
    have ex : x₁ ∈ ({x₂, y₂, w₂} : Finset ℕ) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ex
    have hx : x₁ = x₂ := by
      rcases ex with h | h | h
      · exact h
      · exfalso; omega
      · exfalso; omega
    have ey : y₁ ∈ ({x₂, y₂, w₂} : Finset ℕ) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ey
    have hy : y₁ = y₂ := by
      rcases ey with h | h | h
      · exfalso; omega
      · exact h
      · exfalso; omega
    have ew : w₁ ∈ ({x₂, y₂, w₂} : Finset ℕ) := by
      rw [← hset]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ew
    have hw : w₁ = w₂ := by
      rcases ew with h | h | h
      · exfalso; omega
      · exfalso; omega
      · exact h
    exact Prod.ext (Prod.ext hx hy) hw
  have hcard : s.card = p * (p * p) := by
    have e1 : G + p - G = p := by omega
    have e2 : G + 2 * p - (G + p) = p := by omega
    have e3 : G + 3 * p - (G + 2 * p) = p := by omega
    rw [hsdef, Finset.card_image_of_injOn hinj, hfamdef,
      Finset.card_product, Finset.card_product, hXdef, hYdef,
      hWdef, Nat.card_Ico, Nat.card_Ico, Nat.card_Ico, e1, e2, e3]
    ring
  refine ⟨s, ?_, ?_⟩
  · rw [hcard]; exact hpn
  · -- chaque témoin est valide
    intro N hN
    rw [Finset.mem_image] at hN
    obtain ⟨t, ht, rfl⟩ := hN
    -- valeur de N
    have hNval : witN z T LA (Iset T G t) (uf t)
        = Bf z T G t + 10 ^ J * fibre (uf t) LA :=
      witN_val (Iset T G t) (uf t) hzT
    -- chiffres
    have hNdig : Nat.digits 10 (witN z T LA (Iset T G t) (uf t))
        = (List.replicate z 0 ++ indList T (Iset T G t))
          ++ (List.range LA).map fun e => 1 + uf t e :=
      witN_digits (huf8 t) (hIsub t ht) (hTmem t ht)
    -- divisibilité
    have hNm : m ∣ witN z T LA (Iset T G t) (uf t) := by
      have hzz : ((witN z T LA (Iset T G t) (uf t) : ℕ) : ZMod m)
          = 0 := by
        rw [hNval]
        push_cast
        linear_combination hufres t ht
      exact (CharP.cast_eq_zero_iff (ZMod m) m _).mp hzz
    have hNR : R ∣ witN z T LA (Iset T G t) (uf t) := by
      rw [hNval]
      apply dvd_add
      · have h10zB : (10 : ℕ) ^ z ∣ Bf z T G t := by
          have e : witLo z T (Iset T G t)
              = 10 ^ z * Nat.ofDigits 10 (indList T (Iset T G t)) :=
            witLo_val z T (Iset T G t)
          exact ⟨Nat.ofDigits 10 (indList T (Iset T G t)), e⟩
        exact hR10.trans h10zB
      · exact hR10.trans
          ((pow_dvd_pow 10 hzJ).trans (dvd_mul_right _ _))
    refine ⟨?_, ?_, ?_⟩
    · rw [hnm]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hRc hNR hNm
    · -- longueur = z + T + LA = n
      rw [hNdig, List.length_append, List.length_append,
        List.length_replicate, indList_length, List.length_map,
        List.length_range]
      omega
    · -- somme = s_B + LA + 4LA = n
      rw [hNdig, List.sum_append, List.sum_append]
      have hmapsum :
          ((List.range LA).map fun e => 1 + uf t e).sum
            = LA + 4 * LA := by
        have hfd := fibre_digits (uf t) LA (huf8 t)
        have hfs := fibre_sigma (uf t) LA (huf8 t)
        rw [hufK t] at hfs
        have e : ((List.range LA).map fun e => 1 + uf t e).sum
            = sigma10 (fibre (uf t) LA) := by
          rw [← hfd]; rfl
        rw [e, hfs]
      rw [hmapsum, indList_sum (hIsub t ht), hIcard t ht]
      simp
      omega

-- `table029` est définie dans `A084029Table.lean` (importé
-- ci-dessus) ; le certificat [3,130] est la réunion des
-- certificats `cert_lo` ([3,65]) et `cert_hi` ([66,130]) de
-- `Scratch029_cert_{lo,hi}.lean`, chacun prouvé par
-- `interval_cases` + `decide +kernel` sur son sous-intervalle
-- (un unique interval_cases sur 128 cas dépasse les
-- 60M heartbeats ; `cert_mid` [40,90] reste une
-- contre-validation indépendante de la zone de recouvrement).

theorem table029_ok_all :
    ∀ n ∈ Finset.Icc 3 130,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h3, h130⟩ := hn
  rcases Nat.lt_or_ge n 66 with h65 | h66
  · exact _root_.cert_lo n (Finset.mem_Icc.mpr ⟨h3, by omega⟩)
  · rcases Nat.lt_or_ge n 98 with h97 | h98
    · exact _root_.cert_hi1 n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · rcases Nat.lt_or_ge n 105 with h104 | h105
      · exact _root_.cert_hi2a n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · rcases Nat.lt_or_ge n 114 with h113 | h114
        · exact _root_.cert_hi2b n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        · rcases Nat.lt_or_ge n 122 with h121 | h122
          · exact _root_.cert_hi2c n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          · exact _root_.cert_hi2d n (Finset.mem_Icc.mpr ⟨by omega, h130⟩)

theorem table029_ok (n : ℕ) (h3 : 3 ≤ n) (h130 : n ≤ 130) :
    n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
      ∀ N ∈ table029 n,
        n ∣ N ∧ (Nat.digits 10 N).length = n ∧
          (Nat.digits 10 N).sum = n :=
  table029_ok_all n (Finset.mem_Icc.mpr ⟨h3, h130⟩)

end A084029

open A084029 in
/-- Théorème principal : OEIS A084029 — pour tout n ≥ 3, il
    existe au moins n multiples de n à n chiffres décimaux de
    somme de chiffres n. -/
theorem A084029 (n : ℕ) (hn : 3 ≤ n) :
    ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ N ∈ s,
      n ∣ N ∧ (Nat.digits 10 N).length = n
        ∧ (Nat.digits 10 N).sum = n := by
  by_cases h130 : n ≤ 130
  · obtain ⟨hlen, hnd, hwit⟩ := table029_ok n hn h130
    refine ⟨(table029 n).toFinset, ?_, ?_⟩
    · rwa [List.toFinset_card_of_nodup hnd]
    · intro N hN
      rw [List.mem_toFinset] at hN
      exact hwit N hN
  · exact A084029_large n (Nat.lt_of_not_le h130)
