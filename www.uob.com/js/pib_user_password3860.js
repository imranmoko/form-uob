var AppletOK=false;
	var stat=0;
	var ONCE=false;
   	var idMinLength ; 
	var idMaxLength ; 
	var pwdMinLength; 
   	var pwdMaxLegth ;
   	var RN_String;
   	var Mod_siz;
   	var Pub_String;    
   	var Mod_String; 
	var uobApplet = new UOBApplet();
	
	function setData(rnstr,modsize,pubstr,modstr) {
		//alert("Inside finally");
		RN_String=rnstr;
		Mod_siz=modsize;
		Pub_String=pubstr;
		Mod_String=modstr;
	//	alert("rnstr : " +rnstr + " : Mod_siz : " + Mod_siz);
	//	alert("Mod_String="+Mod_String);
	}
	
	
	function dostoreRSApublickey()
		{
			var errorNum = uobApplet.OBM_SpecifyRSAPublicKey( parseInt (Mod_siz)/8 , Pub_String, Mod_String);
			if(errorNum != 0){
			    return false;
			}
			return true;
	  }
     function doEncryptUserLoginMsg(){
    	// alert('doEncryptUserLoginMsg() Mod_siz:'+ Mod_siz);
	      uobApplet = new UOBApplet();
	    //  alert('doEncryptUserLoginMsg():uobApplet: '+uobApplet +'RN_String:'+RN_String);
      	  dostoreRSApublickey();
		  var C_String = "";    
		  var P_String = "";    
		  var currentPINString = document.getElementById("newPassword").value;  
		  //var currentPINString = document.changeuserpassword.newPassword.value;
		  var currErrorNum = uobApplet.OBM_EncryptPassword(currentPINString, RN_String);
		  
		 // alert('doEncryptUserLoginMsg(): currentPINString:' +currentPINString + 'Error: '+ currErrorNum) ;
		  if (currErrorNum != 0)
		  {
			//  alert('doEncryptUserLoginMsg(): false' );
		    return false;
		  }
		  else
		  {
		    C_String = uobApplet.OBM_GetEncryptedPassword();
		    P_String = uobApplet.OBM_GetEncodingParameter();
		//alert("doEncryptUserLoginMsg:: C_String"+C_String+":P_String:"+P_String);
		    if (C_String != "")
		    {
	    		//document.getElementById("newPassword").value = C_String.toUpperCase();
	    		//document.getElementById("ENCODINGPARAM").value = P_String.toUpperCase();
	    		
	    		document.forceChgUsrPwdHdForm.newHDPassword.value = C_String.toUpperCase();
				document.forceChgUsrPwdHdForm.ENCODINGPARAM.value = P_String.toUpperCase();
				document.forceChgUsrPwdHdForm.newHDUserId.value = document.changeuserpassword.newUserId.value;
	    		//alert("doEncryptUserLoginMsg()"+document.getElementById("newPassword").value);
		    }
		    else
		    {
		    	//alert("FALSE IN ENCRYPTION");
		      return false;
		    }

		  }
	return true;
	}

     function doClearFields(){
    	 document.getElementById("newUserId").value="";
    	 	document.getElementById("newPassword").value="";
    	 	document.getElementById("confirmNewPassword").value=""; 
    	 return true;
     }

  function doClear(){
//	  document.forms[0].newPassword.value = "";

	 // document.getElementById("confirmNewPassword").className ="form-short";
	  document.getElementById('genricErrorDiv').style.display = 'none';
	  return true;
  }	   
   function userNameToUpper() {
   		document.changeuserpassword.newUserId.value = document.changeuserpassword.newUserId.value.toUpperCase();
	}
   
   
   function validateOnSubmit(){ 

		if (formValidation) {
			bSuccess = true;
		} else{
			return false;
		}	
		if (bSuccess) {
			AppletEncription(); 
		
			return true;
		}
	}
  
  function formValidation(){
   		var USER =document.getElementById("newUserId").value;
   		//alert(USER);
   		USER = USER.replace(/^\s+|\s+$/g, '') ;
   		var errArray = new Array(3);
   		var clearArray = new Array(3);
		var i = 0;
		var clVal = 0;
		var isPassWordValidated = true;
		var isUserNameValidated = true;
		var alphaExp = /^[[0-9\_]+$/;
		elem1 = document.getElementById("newUserId");
		elem2 = document.getElementById("newPassword");
		elem3 = document.getElementById("confirmNewPassword");
	//	alert("idMinLength :: "+idMinLength);
	//	alert("idMaxLength :: "+idMaxLength);
		if(isEmpty(elem1.value)){
			isUserNameValidated = false;
		}
		if((elem1.value.length < idMinLength)||(elem1.value.length > idMaxLength))  {
			isUserNameValidated = false;
		}
		if(!isAlphaNumericPassword(elem1.value)){
			isUserNameValidated = false;
		}
		
		if(elem1.value.match(alphaExp)){
			isUserNameValidated = false;
		}
		
		
		if(isEmpty(elem2.value)){
			isPassWordValidated = false;
		}
		if((elem2.value.length < pwdMinLength)||(elem2.value.length > pwdMaxLegth))  {
			isPassWordValidated = false;
		}
		if(!isAlphaNumericPassword(elem2.value)){
			isPassWordValidated = false;
		}
		var alphaExp = /^[a-zA-Z\_]+$/;
		if(elem2.value.match(alphaExp)){
			isPassWordValidated = false;
		}
		var onlydigits = /^[0-9]+$/;
		if(elem2.value.match(onlydigits)) {
			isPassWordValidated = false;
		}
		if(elem2.value != elem3.value){	  	
			isPassWordValidated = false;
	  	}
		
		if(elem1.value.toUpperCase() == elem2.value.toUpperCase()){
			isPassWordValidated = false;
  		}

		if(isPassWordValidated){
			clearArray[clVal] ="newPassword";
			clVal = clVal + 1;
			clearArray[clVal] ="confirmNewPassword";
			clVal = clVal + 1;
		}else{
			errArray[i] ="newPassword";
			i = i + 1;
			errArray[i] ="confirmNewPassword";
			i = i + 1;
    	 //	document.getElementById("newPassword").value="";
    	 //	document.getElementById("confirmNewPassword").value=""; 
		}
		
		if(isUserNameValidated){
			clearArray[clVal] ="newUserId";
		}else{
			i = i + 1;
			errArray[i] ="newUserId";
		//	document.getElementById("newUserId").value="";
		}
		
		if (i > 0) {
			errArray[0] = "newUserId";
			errArray[1] = "newPassword";
			errArray[2] = "confirmNewPassword";
		}
		
		
		pibJSValidationToDefault(clearArray);
		//alert("fubar 2...... ");
		var retVal = pibJSValidation(errArray);
		return retVal;
		
		/*if(i < 1){
				errArray = new Array(0);
		}
		else {
			document.getElementById(errArray[0]).focus();
		}*/
			//var retVal = pibJSValidation(errArray);
		/*var retVal = true;
			alert("END :: retVal :: "+retVal);
			return retVal;*/
 }
   function initApplet() {     
			doClear();
			$("#newPassword").val("");	
}
	function AppletEncription() {
		var validated = false;
		
	//	alert("RN_String, Mod_siz, Pub_String, Mod_String : " + RN_String+" : "+ Mod_siz+" : "+ Pub_String+" : "+ Mod_String);
	$('form[data-validate="parsley"]').each(function () {
	 	// assuming there will be only one form with data-validate=parsley in page scope.
				$('#newUserId').parsley('addConstraint',{'minlength': 8});
				$('#newUserId').parsley('addConstraint',{'maxlength': 16});
				
				$('#newUserId').parsley('addConstraint',{'charonlycheck': 10});
				$('#newUserId').parsley('addConstraint',{'specialchar': 10});
				
				$('#newPassword').parsley('addConstraint',{'minlength': 8});
				$('#newPassword').parsley('addConstraint',{'maxlength': 24});
				
				$('#newPassword').parsley('addConstraint',{'digitcheck': 10});
				$('#newPassword').parsley('addConstraint',{'specialchar': 10});
			//	alert('Before check pwd and username');
				$('#newPassword').parsley('addConstraint',{'checknewpwd':'#newUserId'});
			//	alert('After check pwd and username');
				$('#confirmNewPassword').parsley('addConstraint',{'minlength': 8});
				$('#confirmNewPassword').parsley('addConstraint',{'maxlength': 24});
				$('#confirmNewPassword').parsley('addConstraint',{'specialchar': 10});
				$('#confirmNewPassword').parsley('addConstraint',{'digitcheck': 10});
				$('#confirmNewPassword').parsley('addConstraint',{'confirmnewpwd':'#newPassword'});
		 
	 		  if($(this).parsley().validate()) {
	 			 
					var isValidData = formValidation();
				//	alert(" isValidData :: "+isValidData);
					if (isValidData) {
						doEncryptUserLoginMsg();  
							doClear();
							 document.forms[0].confirmNewPassword.value = "";
							validated = true;
					} else{
						jsSubmitDone = false;
						validated = false;
					}	
			  }
	 		// alert('1::'+validated);
	 		  return validated;
	 	});
	
	validated = formValidation();
	if (validated) {
		doEncryptUserLoginMsg();
		doClearFields();
		//document.forms[0].confirmNewPassword.value = "";
		document.forceChgUsrPwdHdForm.hiddenButton.click();		 
		return false;
	} else{
		//doClearFields();
		validated = false;
	}
 	
	
	
//	alert('2::'+validated);
	 	return validated;
		
		
		
		
		
//		alert("am i even called?");
//		var isValidData=formValidation();
//	//	alert("isValidData :: "+isValidData);
//		if (isValidData) {
//     		bSuccess = true;
//		} else{
//			bSuccess = false;
//			return false;
//		}	
//	//	alert("AppletEncription():" +bSuccess);
//		if (bSuccess) {
//			
//    	doEncryptUserLoginMsg();  
//    //	document.changeuserpassword.newPassword.value=document.changeuserpassword.newPassword.value.replace(/./g,' ');	
//   	//  document.changeuserpassword.newUserId.value =     	document.changeuserpassword.newUserId.value;
//		doClear();
//		  document.forms[0].confirmNewPassword.value = "";
//	return true;
//		}
}